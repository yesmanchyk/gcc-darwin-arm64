/* C++ reflection code.
   Copyright (C) 2025 Free Software Foundation, Inc.
   Written by Marek Polacek <polacek@redhat.com>

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "target.h"
#include "tm.h"
#include "cp-tree.h"
#include "stringpool.h" // for get_identifier
#include "intl.h"

static tree eval_is_function_type (location_t, const constexpr_ctx *, tree,
				   tree *);
struct constexpr_ctx;

static GTY(()) tree vector_identifier;

/* Initialize state for reflection; e.g., initialize meta_info_type_node.  */

void
init_reflection ()
{
  /* The type std::meta::info is a scalar type for which equality and
     inequality are meaningful, but for which no ordering relation is
     defined.  */
  meta_info_type_node = make_node (META_TYPE);
  /* Make it a complete type.  */
  TYPE_SIZE (meta_info_type_node) = bitsize_int (GET_MODE_BITSIZE (ptr_mode));
  TYPE_SIZE_UNIT (meta_info_type_node) = size_int (GET_MODE_SIZE (ptr_mode));
  /* Name it.  */
  record_builtin_type (RID_MAX, "decltype(^^int)", meta_info_type_node);

  vector_identifier = get_identifier ("vector");

  TREE_TYPE (std_meta_node) = void_type_node;
}

/* Create a REFLECT_EXPR expression around T.  */

static tree
get_reflection_raw (location_t loc, tree t)
{
  t = build1_loc (loc, REFLECT_EXPR, meta_info_type_node, t);
  TREE_CONSTANT (t) = true;
  TREE_READONLY (t) = true;
  TREE_SIDE_EFFECTS (t) = false;
  return t;
}

/* Return the reflection for T.

    [basic.fundamental]: A value of type std::meta::info is called a reflection.
    There exists a unique null reflection; every other reflection is
    a representation of

    -- a value of scalar type,
    -- an object with static storage duration,
    -- a variable,
    -- a structured binding,
    -- a function,
    -- a function parameter,
    -- an enumerator,
    -- an annotation,
    -- a type alias,
    -- a type,
    -- a class member,
    -- an unnamed bit-field,
    -- a class template,
    -- a function template,
    -- a variable template,
    -- an alias template,
    -- a concept,
    -- a namespace alias,
    -- a namespace,
    -- a direct base class relationship, or
    -- a data member description.  */

tree
get_reflection (location_t loc, tree t)
{
  STRIP_ANY_LOCATION_WRAPPER (t);

  /* [expr.reflect] If the type-id designates a placeholder type, R is
     ill-formed.  */
  if (is_auto (t))
    {
      error_at (loc, "%<^^%> cannot be applied to a placeholder type");
      return error_mark_node;
    }
  /* Constant template parameters and pack-index-expressions cannot
     appear as operands of the reflection operator.  */
  else if (PACK_INDEX_P (t))
    {
      error_at (loc, "%<^^%> cannot be applied to a pack index");
      return error_mark_node;
    }
  else if (TREE_CODE (t) == CONST_DECL && DECL_TEMPLATE_PARM_P (t))
    {
      error_at (loc, "%<^^%> cannot be applied to a non-type template "
		"parameter %qD", t);
      return error_mark_node;
    }
  /* If the id-expression denotes a local parameter introduced by
     a requires-expression, R is ill-formed.  */
  else if (TREE_CODE (t) == PARM_DECL && CONSTRAINT_VAR_P (t))
    {
      error_at (loc, "%<^^%> cannot be applied to a local parameter of "
		"a requires-expression %qD", t);
      return error_mark_node;
    }
  /* If the id-expression denotes a local entity E for which there is
     a lambda scope that intervenes between R and the point at which E
     was introduced, R is ill-formed.  */
  else if (outer_automatic_var_p (t))
    {
      auto_diagnostic_group d;
      error_at (loc, "%<^^%> cannot be applied a local entity for which "
		"there is an intervening lambda expression");
      inform (DECL_SOURCE_LOCATION (t), "%qD declared here", t);
      return error_mark_node;
    }
  /* If the id-expression denotes a variable declared by an init-capture,
     R is ill-formed.  */
  else if (is_capture_proxy (t) && !is_normal_capture_proxy (t))
    {
      error_at (loc, "%<^^%> cannot be applied to a local entity declared "
		"by init-capture");
      return error_mark_node;
    }
  /* If lookup finds a declaration that replaced a using-declarator during
     a single search, R is ill-formed.  */
  else if (TREE_CODE (t) == USING_DECL
	   || (TREE_CODE (t) == OVERLOAD && OVL_USING_P (t)))
    {
      error_at (loc, "%<^^%> cannot be applied to a using-declarator");
      return error_mark_node;
    }
  /* A concept is fine, but not Concept<arg>.  */
  else if (concept_check_p (t))
    {
      error_at (loc, "%<^^%> cannot be applied to a concept check");
      return error_mark_node;
    }

  /* Otherwise, if the template-name names a function template F,
     then the template-name interpreted as an id-expression shall
     denote an overload set containing only F.  R represents F.

     When we have:
       template<typename T>
       void foo (T) {}
       constexpr auto a = ^^foo;
     we will get an OVERLOAD containing only one function.  */
  tree r = MAYBE_BASELINK_FUNCTIONS (t);
  if (OVL_P (r))
    {
      if (!OVL_SINGLE_P (r))
	{
	  error_at (loc, "cannot take the reflection of an overload set");
	  return error_mark_node;
	}
    }
  /* [expr.reflect] If the id-expression denotes an overload set S,
     overload resolution for the expression &S with no target shall
     select a unique function; R represents that function.  */
  else if (!processing_template_decl)
    {
      /* We can't resolve all TEMPLATE_ID_EXPRs here (due to
	 _postfix_dot_deref_expression) but we can weed out the bad ones.  */
      r = resolve_nondeduced_context_or_error (t, tf_warning_or_error);
      if (r == error_mark_node)
	t = r;
    }

  /* For injected-class-name, use the main variant so that comparing
     reflections works (cf. compare3.C).  */
  if (RECORD_OR_UNION_TYPE_P (t)
      && TYPE_NAME (t)
      && DECL_SELF_REFERENCE_P (TYPE_NAME (t)))
    t = TYPE_MAIN_VARIANT (t);

  if (t == error_mark_node)
    return error_mark_node;

  return get_reflection_raw (loc, t);
}

/* Return a null reflection value.  */

// XXX why not just one static tree?
tree
get_null_reflection ()
{
  return get_reflection_raw (UNKNOWN_LOCATION, unknown_type_node);
}

/* Returns true if FNDECL, a FUNCTION_DECL, is a call to a metafunction
   declared in namespace std::meta.  */

bool
metafunction_p (tree fndecl)
{
  if (!flag_reflection)
    return false;

  /* Metafunctions are expected to be marked consteval.  */
  if (!DECL_IMMEDIATE_FUNCTION_P (fndecl))
    return false;

  if (special_function_p (fndecl))
    return false;

  /* Is the call from std::meta?  */
  fndecl = decl_namespace_context (fndecl);
  return DECL_NAMESPACE_STD_META_P (fndecl);
}

/* Extract the N-th reflection argument from a metafunction call CALL.  */

static tree
get_info (tree call, int n)
{
  gcc_checking_assert (call_expr_nargs (call) > n);
  tree info = get_nth_callarg (call, n);
  gcc_checking_assert (REFLECTION_TYPE_P (TREE_TYPE (info)));
  info = cxx_constant_value (info);
  return info;
}

/* Return std::vector<info>.  */

static tree
get_vector_info ()
{
  tree args = make_tree_vec (1);
  TREE_VEC_ELT (args, 0) = meta_info_type_node;
  tree inst = lookup_template_class (vector_identifier, args,
				     /*in_decl*/NULL_TREE,
				     /*context*/std_node, tf_none);
  inst = complete_type (inst);
  if (inst == error_mark_node || !COMPLETE_TYPE_P (inst))
    {
      error ("couldn%'t look up %qs", "std::vector");
      return NULL_TREE;
    }

  return inst;
}

/* Create std::meta::exception{ what, refl }.  WHAT is the string for what(),
   and REFL is the info for from().  */

static tree
get_meta_exception_object (location_t loc, const char *what, tree refl)
{
  tree type = lookup_qualified_name (std_meta_node, "exception",
				     LOOK_want::TYPE, /*complain*/true);
  if (TREE_CODE (type) != TYPE_DECL || !CLASS_TYPE_P (TREE_TYPE (type)))
    {
      error_at (loc, "couldn%'t throw %qs", "std::meta::exception");
      return NULL_TREE;
    }
  type = TREE_TYPE (type);
  vec<constructor_elt, va_gc> *elts = nullptr;
  tree string_lit = build_string (strlen (what) + 1, what);
  TREE_TYPE (string_lit) = char_array_type_node;
  string_lit = fix_string_type (string_lit);
  CONSTRUCTOR_APPEND_ELT (elts, NULL_TREE, string_lit);
  CONSTRUCTOR_APPEND_ELT (elts, NULL_TREE, get_reflection_raw (loc, refl));
  tree ctor = build_constructor (init_list_type_node, elts);
  CONSTRUCTOR_IS_DIRECT_INIT (ctor) = true;
  TREE_CONSTANT (ctor) = true;
  TREE_STATIC (ctor) = true;
  return finish_compound_literal (type, ctor, tf_warning_or_error,
				  fcl_functional);
}

/* Perform 'throw std::meta::exception{...}'.  WHAT is the string for what(),
   REFL is the reflection for from().  */

static tree
throw_exception (location_t loc, const constexpr_ctx *ctx, const char *what,
		 tree refl, tree *jump_target)
{
  if (tree obj = get_meta_exception_object (loc, what, refl))
    *jump_target = cxa_allocate_and_throw_exception (loc, ctx, obj);
  return NULL_TREE;
}

/* Wrapper around throw_exception, generic case.  */

static tree
throw_exception_generic (location_t loc, const constexpr_ctx *ctx,
			 tree refl, tree *jump_target)
{
  return throw_exception (loc, ctx, N_("Oy vey!"), refl, jump_target);
}

/* Wrapper around throw_exception to complain that the reflection does not
   represent a type.  */

static tree
throw_exception_nontype (location_t loc, const constexpr_ctx *ctx,
			 tree refl, tree *jump_target)
{
  return throw_exception (loc, ctx,
			  N_("reflection does not represent a type"),
			  refl, jump_target);
}

/* Wrapper around throw_exception to complain that the reflection does not
   represent something that satisfies has_template_arguments.  */

static tree
throw_exception_notargs (location_t loc, const constexpr_ctx *ctx,
			 tree refl, tree *jump_target)
{
  return throw_exception (loc, ctx,
			  N_("reflection does not have template arguments"),
			  refl, jump_target);
}

/* Wrapper around throw_exception to complain that the reflection does not
   represent a function or a function type.  */

static tree
throw_exception_nofn (location_t loc, const constexpr_ctx *ctx,
		      tree refl, tree *jump_target)
{
  return throw_exception
    (loc, ctx,
     N_("reflection does not represent a function/function type"),
     refl, jump_target);
}

/* Process std::meta::has_identifier.  Returns:

    (1.1) If r represents an entity that has a typedef name for linkage
	  purposes, then true.
    (1.2) Otherwise, if r represents an unnamed entity, then false.
    (1.3) Otherwise, if r represents a class type, then
	  !has_template_arguments(r).
    (1.4) Otherwise, if r represents a function, then true if
	  !has_template_arguments(r) and the function is not a constructor,
	  destructor, operator function, or conversion function.  Otherwise,
	  false.
    (1.5) Otherwise, if r represents a template, then true if r does not
	  represent a constructor template, operator function template, or
	  conversion function template.  Otherwise, false.
    (1.6) Otherwise, if r represents a variable, then false if the declaration
	  of that variable was instantiated from a function parameter pack.
	  Otherwise, !has_template_arguments(r).
    (1.7) Otherwise, if r represents a structured binding, then false if the
	  declaration of that structured binding was instantiated from
	  a structured binding pack.  Otherwise, true.
    (1.8) Otherwise, if r represents a type alias, then
	  !has_template_arguments(r).
    (1.9) Otherwise, if r represents a enumerator, non-static data member,
	  namespace, or namespace alias, then true.
    (1.10) Otherwise, if r represents a direct base class relationship, then
	   has_identifier(type_of(r)).
    (1.11) Otherwise, r represents a data member description (T, N, A, W, NUA);
	   true if N is not _|_.  Otherwise, false.  */

static tree
eval_has_identifier (const_tree r)
{
  if (TREE_CODE (r) == TYPE_DECL)
    r = TREE_TYPE (r);
  // TODO
  if (CLASS_TYPE_P (r) && TYPE_NAME (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_variable.
   Returns: true if r represents a variable.  Otherwise, false.  */

static tree
eval_is_variable (const_tree r)
{
  /* A parameter is a variable because it is an object or a reference
     introduced by a declaration.  */
  if (TREE_CODE (r) == PARM_DECL
      || (VAR_P (r)
	  /* The definition of a variable excludes non-static data members.  */
	  && !DECL_ANON_UNION_VAR_P (r)
	  /* A structured binding is not a variable.  */
	  && !DECL_DECOMPOSITION_P (r)))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_type.
   Returns: true if r represents an entity whose underlying entity is
   a type.  Otherwise, false.  */

static tree
eval_is_type (const_tree r)
{
  /* Null reflection isn't a type.  */
  if (TYPE_P (r) && r != unknown_type_node)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_type_alias.
   Returns: true if r represents a type alias.  Otherwise, false.  */

static tree
eval_is_type_alias (const_tree r)
{
  if (TYPE_P (r) && typedef_variant_p (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_namespace.
   Returns: true if r represents an entity whose underlying entity is
   a namespace.  Otherwise, false.  */

static tree
eval_is_namespace (const_tree r)
{
  if (TREE_CODE (r) == NAMESPACE_DECL)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_namespace_alias.
   Returns: true if r represents a namespace alias.  Otherwise, false.  */

static tree
eval_is_namespace_alias (const_tree r)
{
  if (TREE_CODE (r) == NAMESPACE_DECL && DECL_NAMESPACE_ALIAS (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_function.
   Returns: true if r represents a function.  Otherwise, false.  */

static tree
eval_is_function (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);

  if (TREE_CODE (r) == FUNCTION_DECL
      /* A destructor.  */
      || (TREE_CODE (r) == BIT_NOT_EXPR && TYPE_P (TREE_OPERAND (r, 0))))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_function_template.
   Returns: true if r represents a function template.  Otherwise, false.  */

static tree
eval_is_function_template (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);

  if (DECL_FUNCTION_TEMPLATE_P (r))
    return boolean_true_node;

  return boolean_false_node;
}

/* Process std::meta::is_variable_template.
   Returns: true if r represents a variable template.  Otherwise, false.  */

static tree
eval_is_variable_template (tree r)
{
  if (variable_template_p (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_class_template.
   Returns: true if r represents a class template.  Otherwise, false.  */

static tree
eval_is_class_template (const_tree r)
{
  if (DECL_CLASS_TEMPLATE_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_alias_template.
   Returns: true if r represents an alias template.  Otherwise, false.  */

static tree
eval_is_alias_template (const_tree r)
{
  if (DECL_ALIAS_TEMPLATE_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_concept.
   Returns: true if r represents a concept.  Otherwise, false.  */

static tree
eval_is_concept (const_tree r)
{
  if (concept_definition_p (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_structured_binding.
   Returns: true if r represents a structured binding.  Otherwise, false.  */

static tree
eval_is_structured_binding (const_tree r)
{
  if (DECL_DECOMPOSITION_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_template.
   Returns: true if r represents a function template, class template, variable
   template, alias template, or concept.  Otherwise, false.  */

static tree
eval_is_template (tree r)
{
  if (eval_is_function_template (r) == boolean_true_node
      || eval_is_class_template (r) == boolean_true_node
      || eval_is_variable_template (r) == boolean_true_node
      || eval_is_alias_template (r) == boolean_true_node
      || eval_is_concept (r) == boolean_true_node)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_function_parameter.
   Returns: true if r represents a function parameter.  Otherwise, false.  */

static tree
eval_is_function_parameter (const_tree r)
{
  if (TREE_CODE (r) == PARM_DECL)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_enumerator.
   Returns: true if r represents an enumerator.  Otherwise, false.  */

static tree
eval_is_enumerator (const_tree r)
{
  /* This doesn't check !DECL_TEMPLATE_PARM_P because such CONST_DECLs
     would already have been rejected.  */
  if (TREE_CODE (r) == CONST_DECL)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_conversion_function.
   Returns: true if r represents a function that is a conversion function.
   Otherwise, false.  */

static tree
eval_is_conversion_function (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL && DECL_CONV_FN_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_operator_function.
   Returns: true if r represents a function that is an operator function.
   Otherwise, false.  */

static tree
eval_is_operator_function (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);

  if (TREE_CODE (r) == FUNCTION_DECL)
    {
      r = OVL_FIRST (r);
      r = STRIP_TEMPLATE (r);
      if (DECL_OVERLOADED_OPERATOR_P (r) && !DECL_CONV_FN_P (r))
	return boolean_true_node;
    }

  return boolean_false_node;
}

/* Process std::meta::is_literal_operator.
   Returns: true if r represents a function that is a literal operator.
   Otherwise, false.  */

static tree
eval_is_literal_operator (const_tree r)
{
  /* No MAYBE_BASELINK_FUNCTIONS here because a literal operator
     must be a non-member function.  */
  if (TREE_CODE (r) == FUNCTION_DECL && UDLIT_OPER_P (DECL_NAME (r)))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_conversion_function_template.
   Returns: true if r represents a conversion function template.
   Otherwise, false.  */

static tree
eval_is_conversion_function_template (const_tree)
{
  // Need members_of to test this.
  gcc_assert (!"TODO");
}

/* Process std::meta::dealias.
   Returns: A reflection representing the underlying entity of what r
   represents.
   Throws: meta::exception unless r represents an entity.  */

static tree
eval_dealias (location_t loc, const constexpr_ctx *ctx, tree r,
	      tree *jump_target)
{
  if (TYPE_P (r) && typedef_variant_p (r))
    r = strip_typedefs (r);
  else if (TREE_CODE (r) == NAMESPACE_DECL)
    r = ORIGINAL_NAMESPACE (r);
  else if (0)
    return throw_exception_generic (loc, ctx, r, jump_target);

  return get_reflection_raw (loc, r);
}

/* Process std::meta::has_template_arguments.
   Returns: true if r represents a specialization of a function template,
   variable template, class template, or an alias template.  Otherwise,
   false.  */

static tree
eval_has_template_arguments (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  /* Presumably for
       typedef cls_tmpl<int> TYPE;
     'has_template_arguments (^^TYPE)' should be false?  */
  if (TYPE_P (r) && typedef_variant_p (r) && !TYPE_ALIAS_P (r))
    return boolean_false_node;
  if (primary_template_specialization_p (r)
      || variable_template_specialization_p (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::template_of.
   Returns: A reflection of the template of the specialization represented
   by r.
   Throws: meta::exception unless has_template_arguments(r) is true.  */

static tree
eval_template_of (location_t loc, const constexpr_ctx *ctx, tree r,
		  tree *jump_target)
{
  if (eval_has_template_arguments (r) != boolean_true_node)
    return throw_exception_notargs (loc, ctx, r, jump_target);

  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TYPE_P (r) && typedef_variant_p (r))
    r = TI_TEMPLATE (TYPE_ALIAS_TEMPLATE_INFO (r));
  else if (CLASS_TYPE_P (r) && CLASSTYPE_TEMPLATE_INFO (r))
    r = CLASSTYPE_TI_TEMPLATE (r);
  else if (VAR_OR_FUNCTION_DECL_P (r) && DECL_TEMPLATE_INFO (r))
    r = DECL_TI_TEMPLATE (r);
  else
    gcc_assert (false);

  gcc_assert (TREE_CODE (r) == TEMPLATE_DECL);
  return get_reflection_raw (loc, r);
}

/* Process std::meta::parameters_of.
   Returns:
   -- If r represents a function F, then a vector containing reflections of
      the parameters of F, in the order in which they appear in a declaration
      of F.
   -- Otherwise, r represents a function type T; a vector containing
      reflections of the types in parameter-type-list of T, in the order in
      which they appear in the parameter-type-list.

   Throws: meta::exception unless r represents a function or a function
   type.  */

static tree
eval_parameters_of (location_t loc, const constexpr_ctx *ctx, tree r,
		    tree *jump_target)
{
  if (!(eval_is_function (r) == boolean_true_node
	|| eval_is_function_type (loc, ctx, r, jump_target)
	    == boolean_true_node))
    return throw_exception_nofn (loc, ctx, r, jump_target);

  r = MAYBE_BASELINK_FUNCTIONS (r);
  vec<constructor_elt, va_gc> *elts = nullptr;
  tree args = (TREE_CODE (r) == FUNCTION_DECL
	       ? FUNCTION_FIRST_USER_PARM (r)
	       : TYPE_ARG_TYPES (r));
  for (tree arg = args; arg && arg != void_list_node; arg = TREE_CHAIN (arg))
    CONSTRUCTOR_APPEND_ELT (elts, NULL_TREE,
			    get_reflection_raw (location_of (arg), arg));
  tree ctor = build_constructor (init_list_type_node, elts);
  CONSTRUCTOR_IS_DIRECT_INIT (ctor) = true;
  TREE_CONSTANT (ctor) = true;
  TREE_STATIC (ctor) = true;
  tree type = get_vector_info ();
  if (!type)
    return error_mark_node;
  r = finish_compound_literal (type, ctor, tf_warning_or_error, fcl_functional);
  if (TREE_CODE (r) == TARGET_EXPR)
    r = TARGET_EXPR_INITIAL (r);
  return r;
}

/* Reflection type traits [meta.reflection.traits].

   Every function and function template declared in this subclause throws
   an exception of type meta::exception unless the following conditions are
   met:
   -- For every parameter p of type info, is_type(p) is true.
   -- For every parameter r whose type is constrained on reflection_range,
      ranges::all_of(r, is_type) is true.  */

/* Evaluate reflection type traits for which we have corresponding built-in
   traits.  KIND says which trait we are interested in; TYPE1 and TYPE2 are
   arguments to the trait.  */

static tree
eval_type_trait (location_t loc, const constexpr_ctx *ctx, tree type1,
		 tree type2, cp_trait_kind kind, tree *jump_target)
{
  if (eval_is_type (type1) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type1, jump_target);
  else if (type2 && eval_is_type (type2) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type2, jump_target);
  tree r = finish_trait_expr (input_location, kind, type1, type2);
  STRIP_ANY_LOCATION_WRAPPER (r);
  return r;
}

/* Like above, but for type traits that take only one type.  */

static tree
eval_type_trait (location_t loc, const constexpr_ctx *ctx, tree type,
		 cp_trait_kind kind, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, NULL_TREE, kind, jump_target);
}

/* Process std::meta::is_function_type.  */

static tree
eval_is_function_type (location_t loc, const constexpr_ctx *ctx, tree type,
		       tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_FUNCTION, jump_target);
}

/* Process std::meta::is_void_type.  */

static tree
eval_is_void_type (location_t loc, const constexpr_ctx *ctx, tree type,
		   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (VOID_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_null_pointer_type.  */

static tree
eval_is_null_pointer_type (location_t loc, const constexpr_ctx *ctx, tree type,
			   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (NULLPTR_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_integral_type.  */

static tree
eval_is_integral_type (location_t loc, const constexpr_ctx *ctx, tree type,
		       tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (CP_INTEGRAL_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_floating_point_type.  */

static tree
eval_is_floating_point_type (location_t loc, const constexpr_ctx *ctx,
			     tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (FLOAT_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_array_type.  */

static tree
eval_is_array_type (location_t loc, const constexpr_ctx *ctx, tree type,
		    tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_ARRAY, jump_target);
}

/* Process std::meta::is_pointer_type.  */

static tree
eval_is_pointer_type (location_t loc, const constexpr_ctx *ctx, tree type,
		      tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_POINTER, jump_target);
}

/* Process std::meta::is_lvalue_reference_type.  */

static tree
eval_is_lvalue_reference_type (location_t loc, const constexpr_ctx *ctx,
			       tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (TYPE_REF_P (type) && !TYPE_REF_IS_RVALUE (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_rvalue_reference_type.  */

static tree
eval_is_rvalue_reference_type (location_t loc, const constexpr_ctx *ctx,
			       tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (TYPE_REF_P (type) && TYPE_REF_IS_RVALUE (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_member_object_pointer_type.  */

static tree
eval_is_member_object_pointer_type (location_t loc, const constexpr_ctx *ctx,
				    tree type, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_MEMBER_OBJECT_POINTER,
			  jump_target);
}

/* Process std::meta::is_member_function_pointer_type.  */

static tree
eval_is_member_function_pointer_type (location_t loc, const constexpr_ctx *ctx,
				      tree type, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_MEMBER_FUNCTION_POINTER,
			  jump_target);
}

/* Process std::meta::is_enum_type.  */

static tree
eval_is_enum_type (location_t loc, const constexpr_ctx *ctx, tree type,
		   tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_ENUM, jump_target);
}

/* Process std::meta::is_union_type.  */

static tree
eval_is_union_type (location_t loc, const constexpr_ctx *ctx, tree type,
		    tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_UNION, jump_target);
}

/* Process std::meta::is_class_type.  */

static tree
eval_is_class_type (location_t loc, const constexpr_ctx *ctx, tree type,
		    tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_CLASS, jump_target);
}

/* Process std::meta::is_reflection_type.  */

static tree
eval_is_reflection_type (location_t loc, const constexpr_ctx *ctx, tree type,
			 tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (REFLECTION_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_reference_type.  */

static tree
eval_is_reference_type (location_t loc, const constexpr_ctx *ctx, tree type,
			tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_REFERENCE, jump_target);
}

/* Process std::meta::is_same_type.  */

static tree
eval_is_same_type (location_t loc, const constexpr_ctx *ctx, tree type1,
		   tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2, CPTK_IS_SAME, jump_target);
}

/* Process std::meta::is_base_of_type.  */

static tree
eval_is_base_of_type (location_t loc, const constexpr_ctx *ctx, tree type1,
		      tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2, CPTK_IS_BASE_OF, jump_target);
}

/* Process std::meta::is_virtual_base_of_type.  */

static tree
eval_is_virtual_base_of_type (location_t loc, const constexpr_ctx *ctx,
			      tree type1, tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2, CPTK_IS_VIRTUAL_BASE_OF,
			  jump_target);
}

/* Process std::meta::is_convertible_type.  */

static tree
eval_is_convertible_type (location_t loc, const constexpr_ctx *ctx,
			  tree type1, tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2, CPTK_IS_CONVERTIBLE,
			  jump_target);
}

/* Process std::meta::is_nothrow_convertible_type.  */

static tree
eval_is_nothrow_convertible_type (location_t loc, const constexpr_ctx *ctx,
				  tree type1, tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2, CPTK_IS_NOTHROW_CONVERTIBLE,
			  jump_target);
}

/* Process std::meta::is_layout_compatible_type.  */

static tree
eval_is_layout_compatible_type (location_t loc, const constexpr_ctx *ctx,
				tree type1, tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2, CPTK_IS_LAYOUT_COMPATIBLE,
			  jump_target);
}

/* Process std::meta::is_pointer_interconvertible_base_of_type.  */

static tree
eval_is_pointer_interconvertible_base_of_type (location_t loc,
					       const constexpr_ctx *ctx,
					       tree type1, tree type2,
					       tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2,
			  CPTK_IS_POINTER_INTERCONVERTIBLE_BASE_OF,
			  jump_target);
}

/* Process std::meta::remove_const.
   Returns: a reflection representing the type denoted by
   std::remove_const_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_remove_const (location_t loc, const constexpr_ctx *ctx, tree type,
		   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  int quals = cp_type_quals (type);
  quals &= ~TYPE_QUAL_CONST;
  type = cp_build_qualified_type (type, quals);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::remove_volatile.
   Returns: a reflection representing the type denoted by
   std::remove_volatile_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_remove_volatile (location_t loc, const constexpr_ctx *ctx, tree type,
		      tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  int quals = cp_type_quals (type);
  quals &= ~TYPE_QUAL_VOLATILE;
  type = cp_build_qualified_type (type, quals);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::remove_cv.
   Returns: a reflection representing the type denoted by
   std::remove_cv_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_remove_cv (location_t loc, const constexpr_ctx *ctx, tree type,
		tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = finish_trait_type (CPTK_REMOVE_CV, type, NULL_TREE, tf_none);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::add_const.
   Returns: a reflection representing the type denoted by
   std::add_const_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_add_const (location_t loc, const constexpr_ctx *ctx, tree type,
		tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  int quals = cp_type_quals (type);
  quals |= TYPE_QUAL_CONST;
  type = cp_build_qualified_type (type, quals);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::add_volatile.
   Returns: a reflection representing the type denoted by
   std::add_volatile_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_add_volatile (location_t loc, const constexpr_ctx *ctx, tree type,
		   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  int quals = cp_type_quals (type);
  quals |= TYPE_QUAL_VOLATILE;
  type = cp_build_qualified_type (type, quals);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::add_cv.
   Returns: a reflection representing the type denoted by
   std::add_cv_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_add_cv (location_t loc, const constexpr_ctx *ctx, tree type,
	     tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  int quals = cp_type_quals (type);
  quals |= (TYPE_QUAL_CONST | TYPE_QUAL_VOLATILE);
  type = cp_build_qualified_type (type, quals);
  return get_reflection_raw (loc, type);
}

/* Expand a call to a metafunction.  CALL is the CALL_EXPR.
   JUMP_TARGET is set if we are throwing std::meta::exception.  */

// TODO Use gperf?
tree
process_metafunction (const constexpr_ctx *ctx, tree call, tree *jump_target)
{
  tree info = get_info (call, 0);
  tree name = DECL_NAME (cp_get_callee_fndecl_nofold (call));
  const char *ident = IDENTIFIER_POINTER (name);
  tree h = REFLECT_EXPR_HANDLE (info);
  const location_t loc = cp_expr_loc_or_input_loc (info);

  /* There still could be a TEMPLATE_ID_EXPR denoting a function template.  */
  h = resolve_nondeduced_context (h, tf_warning_or_error);

  /* Handle is_*.  */
  if (startswith (ident, "is_"))
    {
      ident += 3;
      if (!strcmp (ident, "variable"))
	return eval_is_variable (h);
      if (!strcmp (ident, "type"))
	return eval_is_type (h);
      if (!strcmp (ident, "type_alias"))
	return eval_is_type_alias (h);
      if (!strcmp (ident, "namespace"))
	return eval_is_namespace (h);
      if (!strcmp (ident, "namespace_alias"))
	return eval_is_namespace_alias (h);
      if (!strcmp (ident, "function"))
	return eval_is_function (h);
      if (!strcmp (ident, "function_template"))
	return eval_is_function_template (h);
      if (!strcmp (ident, "variable_template"))
	return eval_is_variable_template (h);
      if (!strcmp (ident, "class_template"))
	return eval_is_class_template (h);
      if (!strcmp (ident, "alias_template"))
	return eval_is_alias_template (h);
      if (!strcmp (ident, "concept"))
	return eval_is_concept (h);
      if (!strcmp (ident, "structured_binding"))
	return eval_is_structured_binding (h);
      if (!strcmp (ident, "template"))
	return eval_is_template (h);
      if (!strcmp (ident, "function_parameter"))
	return eval_is_function_parameter (h);
      if (!strcmp (ident, "enumerator"))
	return eval_is_enumerator (h);
      if (!strcmp (ident, "conversion_function"))
	return eval_is_conversion_function (h);
      if (!strcmp (ident, "operator_function"))
	return eval_is_operator_function (h);
      if (!strcmp (ident, "literal_operator"))
	return eval_is_literal_operator (h);
      if (!strcmp (ident, "conversion_function_template"))
	return eval_is_conversion_function_template (h);
      if (!strcmp (ident, "function_type"))
	return eval_is_function_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "void_type"))
	return eval_is_void_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "null_pointer_type"))
	return eval_is_null_pointer_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "integral_type"))
	return eval_is_integral_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "floating_point_type"))
	return eval_is_floating_point_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "array_type"))
	return eval_is_array_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "pointer_type"))
	return eval_is_pointer_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "lvalue_reference_type"))
	return eval_is_lvalue_reference_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "rvalue_reference_type"))
	return eval_is_rvalue_reference_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "member_object_pointer_type"))
	return eval_is_member_object_pointer_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "member_function_pointer_type"))
	return eval_is_member_function_pointer_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "enum_type"))
	return eval_is_enum_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "union_type"))
	return eval_is_union_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "class_type"))
	return eval_is_class_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "reflection_type"))
	return eval_is_reflection_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "reference_type"))
	return eval_is_reference_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "same_type"))
	{
	  tree h1 = REFLECT_EXPR_HANDLE (get_info (call, 1));
	  return eval_is_same_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "base_of_type"))
	{
	  tree h1 = REFLECT_EXPR_HANDLE (get_info (call, 1));
	  return eval_is_base_of_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "virtual_base_of_type"))
	{
	  tree h1 = REFLECT_EXPR_HANDLE (get_info (call, 1));
	  return eval_is_virtual_base_of_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "convertible_type"))
	{
	  tree h1 = REFLECT_EXPR_HANDLE (get_info (call, 1));
	  return eval_is_convertible_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "nothrow_convertible_type"))
	{
	  tree h1 = REFLECT_EXPR_HANDLE (get_info (call, 1));
	  return eval_is_nothrow_convertible_type (loc, ctx, h, h1,
						   jump_target);
	}
      if (!strcmp (ident, "layout_compatible_type"))
	{
	  tree h1 = REFLECT_EXPR_HANDLE (get_info (call, 1));
	  return eval_is_layout_compatible_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "pointer_interconvertible_base_of_type"))
	{
	  tree h1 = REFLECT_EXPR_HANDLE (get_info (call, 1));
	  return eval_is_pointer_interconvertible_base_of_type (loc, ctx, h, h1,
								jump_target);
	}
      goto not_found;
    }

  /* Handle has_*.  */
  if (startswith (ident, "has_"))
    {
      ident += 4;
      if (!strcmp (ident, "identifier"))
	return eval_has_identifier (h);
      if (!strcmp (ident, "template_arguments"))
	return eval_has_template_arguments (h);
      goto not_found;
    }

  if (id_equal (name, "dealias"))
    return eval_dealias (loc, ctx, h, jump_target);
  if (id_equal (name, "template_of"))
    return eval_template_of (loc, ctx, h, jump_target);
  if (id_equal (name, "parameters_of"))
    return eval_parameters_of (loc, ctx, h, jump_target);
  if (id_equal (name, "remove_const"))
    return eval_remove_const (loc, ctx, h, jump_target);
  if (id_equal (name, "remove_volatile"))
    return eval_remove_volatile (loc, ctx, h, jump_target);
  if (id_equal (name, "remove_cv"))
    return eval_remove_cv (loc, ctx, h, jump_target);
  if (id_equal (name, "add_const"))
    return eval_add_const (loc, ctx, h, jump_target);
  if (id_equal (name, "add_volatile"))
    return eval_add_volatile (loc, ctx, h, jump_target);
  if (id_equal (name, "add_cv"))
    return eval_add_cv (loc, ctx, h, jump_target);

not_found:
  sorry ("%qE", name);
  return NULL_TREE;
}

/* Splice reflection REFL; i.e., return its entity.  */

tree
splice (tree refl)
{
  if (refl == error_mark_node)
    return error_mark_node;

  /* Who in the world am I?  That's the great puzzle and we have to wait
     until instantiation to find out.  */
  if (instantiation_dependent_expression_p (refl))
    return build_nt (SPLICE_EXPR, refl);

  /* [basic.splice] "The constant-expression of a splice-specifier shall
     be a converted constant expression of type std::meta::info."  */
  refl = build_converted_constant_expr (meta_info_type_node, refl,
					tf_warning_or_error);

  refl = cxx_constant_value (refl);
  if (!REFLECT_EXPR_P (refl))
    /* I don't wanna do your dirty work no more.  */
    return error_mark_node;

  return REFLECT_EXPR_HANDLE (refl);
}

/* A walker for consteval_only_p.  It cannot be a lambda, because we
   have to call this recursively, sigh.  */

static tree
consteval_only_type_r (tree *tp, int *, void *data)
{
  tree t = *tp;
  /* Types can contain themselves recursively, hence this.  */
  auto visited = static_cast<hash_set<tree> *>(data);

  if (!TYPE_P (t))
    return NULL_TREE;

  if (REFLECTION_TYPE_P (t))
    return t;

  if (RECORD_OR_UNION_TYPE_P (t))
    for (tree member = TYPE_FIELDS (t);
	 member; member = DECL_CHAIN (member))
      if (TREE_CODE (member) == FIELD_DECL)
	if (tree r = cp_walk_tree (&TREE_TYPE (member), consteval_only_type_r,
				   visited, visited))
	  return r;

  return NULL_TREE;
}

/* True if T is a consteval-only type as per [basic.types.general]:
   "A type is consteval-only if it is either std::meta::info or a type
   compounded from a consteval-only type", or something that has
   a consteval-only type.  */

bool
consteval_only_p (tree t)
{
  if (!flag_reflection)
    return false;

  /* cp_walk_tree walks template arguments, but
     std::initializer_list<std::meta::info>::size_type should be fine,
     or a nullptr constant, and similar.  */
  if (TREE_CODE (t) == INTEGER_CST)
    return false;

  if (!TYPE_P (t))
    t = TREE_TYPE (t);

  /* Classes with std::meta::info members are also consteval-only.  */
  hash_set<tree> visited;
  return !!cp_walk_tree (&t, consteval_only_type_r, &visited, &visited);
}

/* Give an error if a consteval-only expression EXPR, or a consteval-only
   variable EXPR not declared constexpr/constinit) is used outside
   a manifestly constant-evaluated context.  E.g.:

     void f() {
       constexpr auto r = ^^int;  // OK
       [: r :] i = 42;  // still OK
       auto z = r;  // bad
     }

   But

     consteval void g() {
       constexpr auto r = ^^int;
       auto z = r;
     }

   is OK.  Return true if we found a problem.  */

bool
check_out_of_consteval_use (tree expr)
{
  if (!flag_reflection || in_immediate_context ())
    return false;

  /* Don't complain if we're generating the body for a synthesized method.  */
  if (current_function_decl)
    {
      if (DECL_CONSTRUCTOR_P (current_function_decl)
	  && DECL_ARTIFICIAL (current_function_decl))
	return false;
      tree ctx = decl_namespace_context (current_function_decl);
      if (DECL_NAMESPACE_STD_META_P (ctx))
	return false;
    }

  auto walker = [](tree *tp, int *walk_subtrees, void *) -> tree
    {
      tree t = *tp;

      /* No need to look into types or unevaluated operands.  */
      if (TYPE_P (t)
	  || unevaluated_p (TREE_CODE (t))
	  /* Don't walk INIT_EXPRs, because we'd emit bogus errors about
	     member initializers.  */
	  || TREE_CODE (t) == INIT_EXPR
	  || TREE_CODE (t) == BIND_EXPR
	  || TREE_CODE (t) == DECL_EXPR)
	{
	  *walk_subtrees = false;
	  return NULL_TREE;
	}

      /* A subexpression of a manifestly constant-evaluated expression is
	 an immediate function context.  For example,

	   consteval void foo (std::meta::info) { }
	   void g() { foo (^^void); }

	 is all good.  */
      if (tree decl = cp_get_callee_fndecl_nofold (t))
	if (immediate_invocation_p (decl))
	  {
	    *walk_subtrees = false;
	    return NULL_TREE;
	  }

      if (VAR_P (t)
	  && (DECL_DECLARED_CONSTEXPR_P (t) || DECL_DECLARED_CONSTINIT_P (t)))
	/* This is fine, don't bother checking the type.  */
	return NULL_TREE;

      /* Now check the type to see if we are dealing with a consteval-only
	 expression.  */
      if (!consteval_only_p (t))
	return NULL_TREE;

      if (current_function_decl
	  /* Already escalated.  */
	  && (DECL_IMMEDIATE_FUNCTION_P (current_function_decl)
	      /* These functions are magic.  */
	      || is_std_allocator_allocate (current_function_decl)))
	{
	  *walk_subtrees = false;
	  return NULL_TREE;
	}

      /* We might have to escalate if we are in an immediate-escalating
	 function.  */
      if (immediate_escalating_function_p (current_function_decl))
	{
	  promote_function_to_consteval (current_function_decl);
	  *walk_subtrees = false;
	  return NULL_TREE;
	}

      /* Yep, gotta complain.  */
      if (VAR_P (t))
	{
	  auto_diagnostic_group d;
	  error_at (cp_expr_loc_or_input_loc (t),
		    "consteval-only variable %qD not declared %<constexpr%> "
		    "used outside a constant-evaluated context", t);
	  if (TREE_STATIC (t) || CP_DECL_THREAD_LOCAL_P (t))
	    inform (DECL_SOURCE_LOCATION (t), "add %<constexpr%> or "
		    "%<constinit%>");
	  else
	    inform (DECL_SOURCE_LOCATION (t), "add %<constexpr%>");
	}
      else
	error_at (cp_expr_loc_or_input_loc (t),
		  "consteval-only expressions are only allowed in "
		  "a constant-evaluated context");

      *walk_subtrees = false;
      return t;
    };

  return !!cp_walk_tree_without_duplicates (&expr, walker, nullptr);
}

/* Return true if the reflections LHS and RHS are equal.  */

bool
compare_reflections (const_tree lhs, const_tree rhs)
{
  tree l = REFLECT_EXPR_HANDLE (lhs);
  tree r = REFLECT_EXPR_HANDLE (rhs);

  r = MAYBE_BASELINK_FUNCTIONS (r);
  l = MAYBE_BASELINK_FUNCTIONS (l);

  /* TEMPLATE_DECLs are wrapped in an OVERLOAD.  When we have

       template_of (^^fun_tmpl<int>) == ^^fun_tmpl

     the RHS will be OVERLOAD<TEMPLATE_DECL> but the LHS will
     only be TEMPLATE_DECL.  They should compare equal, though.  */
  // ??? Can we do something better?
  return OVL_FIRST (l) == OVL_FIRST (r);
}

/* Return true if T is a valid splice-type-specifier.
   [dcl.type.splice]: For a splice-type-specifier of the form
   "typename[opt] splice-specifier", the splice-specifier shall designate
   a type, a class template, or an alias template.
   For a splice-type-specifier of the form
   "typename[opt] splice-specialization-specifier", the splice-specifier
   of the splice-specialization-specifier shall designate a template T
   that is either a class template or an alias template.  */

bool
valid_splice_type_p (const_tree t)
{
  return TYPE_P (t);
}

/* Return true if T is a valid splice-scope-specifier.
   [basic.lookup.qual.general]: If a splice-scope-specifier is followed
   by a ::, it shall either be a dependent splice-scope-specifier or it
   shall designate a namespace, class, enumeration, or dependent type.  */

bool
valid_splice_scope_p (const_tree t)
{
  return (CLASS_TYPE_P (t)
	  || TREE_CODE (t) == ENUMERAL_TYPE
	  || TREE_CODE (t) == NAMESPACE_DECL);
}

/* Return true if T is a valid result of splice-expression.  */

bool
valid_splice_expr_p (const_tree t)
{
  if (TREE_CODE (t) == TYPE_DECL
      || TREE_CODE (t) == NAMESPACE_DECL
      || TYPE_P (t))
    return false;

  return true;
}

/* Create a new SPLICE_SCOPE tree.  EXPR is its SPLICE_SCOPE_EXPR, and
   TYPE_P says if it should have SPLICE_SCOPE_TYPE_P set.  */

tree
make_splice_scope (tree expr, bool type_p)
{
  tree t = cxx_make_type (SPLICE_SCOPE);
  SPLICE_SCOPE_EXPR (t) = expr;
  SPLICE_SCOPE_TYPE_P (t) = type_p;
  return t;
}

/* Return true if T is a splice expression; that is, it is either [:T:] or
   [:T:]<arg>.  */

bool
dependent_splice_p (const_tree t)
{
  return (TREE_CODE (t) == SPLICE_EXPR
	  || (TREE_CODE (t) == TEMPLATE_ID_EXPR
	      && TREE_CODE (TREE_OPERAND (t, 0)) == SPLICE_EXPR));
}
