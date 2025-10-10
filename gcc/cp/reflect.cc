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
#include "attribs.h"

static tree eval_is_function_type (location_t, const constexpr_ctx *, tree,
				   tree *);
static tree eval_is_object_type (location_t, const constexpr_ctx *, tree,
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

/* Create a REFLECT_EXPR expression of kind KIND around T.  */

static tree
get_reflection_raw (location_t loc, tree t, reflect_kind kind = REFLECT_UNDEF)
{
  t = build1_loc (loc, REFLECT_EXPR, meta_info_type_node, t);
  REFLECT_EXPR_KIND (t) = kind;
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
    -- a data member description.

   KIND is used to distinguish between categories that are represented
   by the same handle.  */

tree
get_reflection (location_t loc, tree t, reflect_kind kind/*=REFLECT_UNDEF*/)
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

  return get_reflection_raw (loc, t, kind);
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
get_info (const constexpr_ctx *ctx, tree call, int n, bool *non_constant_p,
	  bool *overflow_p, tree *jump_target)
{
  gcc_checking_assert (call_expr_nargs (call) > n);
  tree info = get_nth_callarg (call, n);
  gcc_checking_assert (REFLECTION_TYPE_P (TREE_TYPE (info)));
  info = cxx_eval_constant_expression (ctx, info, vc_prvalue,
				       non_constant_p, overflow_p,
				       jump_target);
  if (*jump_target)
    return NULL_TREE;
  if (!REFLECT_EXPR_P (info))
    {
      *non_constant_p = true;
      return NULL_TREE;
    }
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

/* The values of std::meta::operators enumerators corresponding to
   the ovl_op_code and IDENTIFIER_ASSIGN_OP_P pair.  */

static unsigned char meta_operators[2][OVL_OP_MAX];

/* Init the meta_operators table if not yet initialized.  */

static void
maybe_init_meta_operators (location_t loc)
{
  if (meta_operators[0][OVL_OP_ERROR_MARK])
    return;
  meta_operators[0][OVL_OP_ERROR_MARK] = 1;
  tree operators = lookup_qualified_name (std_meta_node, "operators");
  if (TREE_CODE (operators) != TYPE_DECL
      || TREE_CODE (TREE_TYPE (operators)) != ENUMERAL_TYPE)
    {
    fail:
      error_at (loc, "unexpected %<std::meta::operators%>");
      return;
    }
  char buf[sizeof "op_greater_greater_equals"];
  memcpy (buf, "op_", 3);
  for (int i = 0; i < 2; ++i)
    for (int j = OVL_OP_ERROR_MARK + 1; j < OVL_OP_MAX; ++j)
      if (ovl_op_info[i][j].meta_name)
	{
	  strcpy (buf + 3, ovl_op_info[i][j].meta_name);
	  tree id = get_identifier (buf);
	  tree t = lookup_enumerator (TREE_TYPE (operators), id);
	  if (t == NULL_TREE || TREE_CODE (t) != CONST_DECL)
	    goto fail;
	  tree v = DECL_INITIAL (t);
	  if (!tree_fits_uhwi_p (v) || tree_to_uhwi (v) > UCHAR_MAX)
	    goto fail;
	  meta_operators[i][j] = tree_to_uhwi (v);
	}
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

/* Process std::meta::source_location_of.
   Returns: If r represents a value, a type other than a class type or an
   enumeration type, the global namespace, or a data member description,
   then source_location{}.  Otherwise, an implementation-defined
   source_location value.  */

static tree
eval_source_location_of (location_t loc, const_tree r,
			 tree std_source_location)
{
  if (!NON_UNION_CLASS_TYPE_P (std_source_location))
    {
      error_at (loc, "%qT is not a class type", std_source_location);
      return error_mark_node;
    }
  location_t rloc = UNKNOWN_LOCATION;
  if (OVERLOAD_TYPE_P (r) || (TYPE_P (r) && typedef_variant_p (r)))
    rloc = DECL_SOURCE_LOCATION (TYPE_NAME (r));
  else if (DECL_P (r) && r != global_namespace)
    rloc = DECL_SOURCE_LOCATION (r);
  tree decl = NULL_TREE, field = NULL_TREE;
  if (rloc != UNKNOWN_LOCATION)
    {
      /* Make sure __builtin_source_location (which depends on
	 std::source_location::__impl) will work without errors.  */
      tree name = get_identifier ("__impl");
      decl = lookup_qualified_name (std_source_location, name);
      if (TREE_CODE (decl) != TYPE_DECL)
	decl = NULL_TREE;
      else
	{
	  name = get_identifier ("__builtin_source_location");
	  decl = lookup_qualified_name (global_namespace, name);
	  if (TREE_CODE (decl) != FUNCTION_DECL
	      || !fndecl_built_in_p (decl, BUILT_IN_FRONTEND)
	      || DECL_FE_FUNCTION_CODE (decl) != CP_BUILT_IN_SOURCE_LOCATION
	      || !require_deduced_type (decl, tf_warning_or_error))
	    decl = NULL_TREE;
	}
    }
  if (decl)
    {
      field = TYPE_FIELDS (std_source_location);
      field = next_aggregate_field (field);
      /* Make sure std::source_location has exactly a single non-static
	 data member (_M_impl in libstdc++, __ptr_ in libc++) with pointer
	 type.  Return {._M_impl = &*.Lsrc_locN}.  */
      if (field != NULL_TREE
	  && POINTER_TYPE_P (TREE_TYPE (field))
	  && !next_aggregate_field (DECL_CHAIN (field)))
	{
	  tree call = build_call_nary (TREE_TYPE (TREE_TYPE (decl)), decl, 0);
	  SET_EXPR_LOCATION (call, rloc);
	  call = fold_builtin_source_location (call);
	  return build_constructor_single (std_source_location, field, call);
	}
    }
  return build_constructor (std_source_location, nullptr);
}

/* Process std::meta::is_variable.
   Returns: true if r represents a variable.  Otherwise, false.  */

static tree
eval_is_variable (const_tree r, reflect_kind kind)
{
  /* ^^param is a variable but parameters_of(parent_of(^^param))[0] is not.  */
  if ((TREE_CODE (r) == PARM_DECL && kind != REFLECT_PARM)
      || (VAR_P (r)
	  /* The definition of a variable excludes non-static data members.  */
	  && !DECL_ANON_UNION_VAR_P (r)
	  /* A structured binding is not a variable.  */
	  && !(DECL_DECOMPOSITION_P (r) && !DECL_DECOMP_IS_BASE (r))))
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

/* Process std::meta::is_object.
   Returns: true if r represents an object.  Otherwise, false.  */

static tree
eval_is_object (reflect_kind kind)
{
  if (kind == REFLECT_OBJECT)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_structured_binding.
   Returns: true if r represents a structured binding.  Otherwise, false.  */

static tree
eval_is_structured_binding (const_tree r)
{
  if (DECL_DECOMPOSITION_P (r) && !DECL_DECOMP_IS_BASE (r))
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
eval_is_function_parameter (const_tree r, reflect_kind kind)
{
  if (kind == REFLECT_PARM)
    {
      gcc_checking_assert (TREE_CODE (r) == PARM_DECL);
      return boolean_true_node;
    }
  else
    return boolean_false_node;
}

/* Process std::meta::is_explicit_object_parameter.
   Returns: true if r represents a function parameter that is an explicit
   object parameter.  Otherwise, false.  */

static tree
eval_is_explicit_object_parameter (const_tree r, reflect_kind kind)
{
  if (eval_is_function_parameter (r, kind) == boolean_true_node
      && r == DECL_ARGUMENTS (DECL_CONTEXT (r))
      && DECL_XOBJ_MEMBER_FUNCTION_P (DECL_CONTEXT (r)))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_ellipsis_parameter.
   Returns: true if r represents a function or function type that has an
   ellipsis in its parameter-type-list.  Otherwise, false.  */

static tree
eval_has_ellipsis_parameter (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL)
    r = TREE_TYPE (r);
  if (FUNC_OR_METHOD_TYPE_P (r)
      // TODO: TYPE_ARG_TYPES check shouldn't be necessary once we
      // implement va_start (ap) support and set TYPE_NO_NAMED_ARGS_STDARG_P.
      // Though wonder if that won't be an ABI change.
      && (stdarg_p (r) || TYPE_ARG_TYPES (r) == NULL_TREE))
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

/* Process std::meta::has_internal_linkage.
   Returns: true if r represents a variable, function, type, template, or
   namespace whose name has internal linkage.  Otherwise, false.  */

static tree
eval_has_internal_linkage (tree r, reflect_kind kind)
{
  if (eval_is_variable (r, kind) == boolean_false_node
      && eval_is_function (r) == boolean_false_node
      && eval_is_type (r) == boolean_false_node
      && eval_is_template (r) == boolean_false_node
      && eval_is_namespace (r) == boolean_false_node)
    return boolean_false_node;
  r = STRIP_TEMPLATE (r);
  if (TYPE_P (r))
    {
      if (TYPE_NAME (r) == NULL_TREE || !DECL_P (TYPE_NAME (r)))
	return boolean_false_node;
      r = TYPE_NAME (r);
    }
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (decl_linkage (r) == lk_internal)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_module_linkage.
   Returns: true if r represents a variable, function, type, template, or
   namespace whose name has module linkage.  Otherwise, false.  */

static tree
eval_has_module_linkage (tree r, reflect_kind kind)
{
  if (eval_is_variable (r, kind) == boolean_false_node
      && eval_is_function (r) == boolean_false_node
      && eval_is_type (r) == boolean_false_node
      && eval_is_template (r) == boolean_false_node
      && eval_is_namespace (r) == boolean_false_node)
    return boolean_false_node;
  r = STRIP_TEMPLATE (r);
  if (TYPE_P (r))
    {
      if (TYPE_NAME (r) == NULL_TREE || !DECL_P (TYPE_NAME (r)))
	return boolean_false_node;
      r = TYPE_NAME (r);
    }
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (decl_linkage (r) == lk_external
      && DECL_LANG_SPECIFIC (r)
      && DECL_MODULE_ATTACH_P (r)
      && !DECL_MODULE_EXPORT_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_external_linkage.
   Returns: true if r represents a variable, function, type, template, or
   namespace whose name has external linkage.  Otherwise, false.  */

static tree
eval_has_external_linkage (tree r, reflect_kind kind)
{
  if (eval_is_variable (r, kind) == boolean_false_node
      && eval_is_function (r) == boolean_false_node
      && eval_is_type (r) == boolean_false_node
      && eval_is_template (r) == boolean_false_node
      && eval_is_namespace (r) == boolean_false_node)
    return boolean_false_node;
  r = STRIP_TEMPLATE (r);
  if (TYPE_P (r))
    {
      if (TYPE_NAME (r) == NULL_TREE || !DECL_P (TYPE_NAME (r)))
	return boolean_false_node;
      r = TYPE_NAME (r);
    }
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (decl_linkage (r) == lk_external
      && !(DECL_LANG_SPECIFIC (r)
	   && DECL_MODULE_ATTACH_P (r)
	   && !DECL_MODULE_EXPORT_P (r)))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_c_language_linkage.
   Returns: true if r represents a variable, function, type, template, or
   namespace whose name has C language linkage.  Otherwise, false.  */

static tree
eval_has_c_language_linkage (tree r, reflect_kind kind)
{
  if (eval_is_variable (r, kind) == boolean_false_node
      && eval_is_function (r) == boolean_false_node
      && eval_is_type (r) == boolean_false_node
      && eval_is_template (r) == boolean_false_node
      && eval_is_namespace (r) == boolean_false_node)
    return boolean_false_node;
  r = STRIP_TEMPLATE (r);
  if (TYPE_P (r))
    {
      if (TYPE_NAME (r) == NULL_TREE || !DECL_P (TYPE_NAME (r)))
	return boolean_false_node;
      r = TYPE_NAME (r);
    }
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) != NAMESPACE_DECL
      && decl_linkage (r) == lk_external
      && DECL_LANGUAGE (r) == lang_c)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_linkage.
   Returns: true if r represents a variable, function, type, template, or
   namespace whose name has any linkage.  Otherwise, false.  */

static tree
eval_has_linkage (tree r, reflect_kind kind)
{
  if (eval_is_variable (r, kind) == boolean_false_node
      && eval_is_function (r) == boolean_false_node
      && eval_is_type (r) == boolean_false_node
      && eval_is_template (r) == boolean_false_node
      && eval_is_namespace (r) == boolean_false_node)
    return boolean_false_node;
  r = STRIP_TEMPLATE (r);
  if (TYPE_P (r))
    {
      if (TYPE_NAME (r) == NULL_TREE || !DECL_P (TYPE_NAME (r)))
	return boolean_false_node;
      r = TYPE_NAME (r);
    }
  if (decl_linkage (r) != lk_none)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_complete_type.
   Returns: true if is_type(r) is true and there is some point in the
   evaluation context from which the type represented by dealias(r) is
   not an incomplete type.  Otherwise, false.  */

static tree
eval_is_complete_type (const_tree r)
{
  if (eval_is_type (r) == boolean_true_node)
    {
      r = strip_typedefs (const_cast<tree> (r));
      complete_type (const_cast<tree> (r));
      if (COMPLETE_TYPE_P (r))
	return boolean_true_node;
    }
  return boolean_false_node;
}

/* Process std::meta::is_enumerable_type.
   A type T is enumerable from a point P if either
   -- T is a class type complete at point P or
   -- T is an enumeration type defined by a declaration D such that D is
      reachable from P but P does not occur within an enum-specifier of D.
  Returns: true if dealias(r) represents a type that is enumerable from some
  point in the evaluation context.  Otherwise, false.  */

static tree
eval_is_enumerable_type (const_tree r)
{
  if (CLASS_TYPE_P (r))
    {
      complete_type (const_cast<tree> (r));
      if (COMPLETE_TYPE_P (r))
	return boolean_true_node;
     }
  else if (TREE_CODE (r) == ENUMERAL_TYPE)
    {
      r = TYPE_MAIN_VARIANT (r);
      if (!ENUM_IS_OPAQUE (r) && !ENUM_BEING_DEFINED_P (r))
	return boolean_true_node;
    }
  return boolean_false_node;
}

/* Process std::meta::is_annotation.
   Returns: true if r represents an annotation.  Otherwise, false.  */

static tree
eval_is_annotation (const_tree r)
{
  if (TREE_CODE (r) == TREE_LIST
      && TREE_PURPOSE (r)
      && get_attribute_namespace (r) == internal_identifier
      && get_attribute_name (r) == annotation_identifier)
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
  r = OVL_FIRST (r);

  if (TREE_CODE (r) == FUNCTION_DECL)
    {
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

/* Process std::meta::is_special_member_function.
   Returns: true if r represents a function that is a special member function.
   Otherwise, false.  */

static tree
eval_is_special_member_function (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL && special_memfn_p (r) != sfk_none)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_constructor.
   Returns: true if r represents a function that is a constructor.
   Otherwise, false.  */

static tree
eval_is_constructor (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL && DECL_CONSTRUCTOR_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_default_constructor.
   Returns: true if r represents a function that is a default constructor.
   Otherwise, false.  */

static tree
eval_is_default_constructor (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL && default_ctor_p (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_copy_constructor.
   Returns: true if r represents a function that is a copy constructor.
   Otherwise, false.  */

static tree
eval_is_copy_constructor (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL && DECL_COPY_CONSTRUCTOR_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_move_constructor.
   Returns: true if r represents a function that is a move constructor.
   Otherwise, false.  */

static tree
eval_is_move_constructor (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL && DECL_MOVE_CONSTRUCTOR_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_assignment.
   Returns: true if r represents a function that is an assignment operator.
   Otherwise, false.  */

static tree
eval_is_assignment (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL
      && DECL_ASSIGNMENT_OPERATOR_P (r)
      && DECL_OVERLOADED_OPERATOR_IS (r, NOP_EXPR))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_copy_assignment.
   Returns: true if r represents a function that is a copy assignment
   operator.  Otherwise, false.  */

static tree
eval_is_copy_assignment (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL
      && special_function_p (r) == sfk_copy_assignment)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_move_assignment.
   Returns: true if r represents a function that is a move assignment
   operator.  Otherwise, false.  */

static tree
eval_is_move_assignment (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL
      && special_function_p (r) == sfk_move_assignment)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_destructor.
   Returns: true if r represents a function that is a destructor.
   Otherwise, false.  */

static tree
eval_is_destructor (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL
      && DECL_MAYBE_IN_CHARGE_DESTRUCTOR_P (r))
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

/* Process std::meta::operator_of.
   Returns: The value of the enumerator from the operators whose corresponding
   operator-function-id is the unqualified name of the entity represented by
   r.
   Throws: meta::exception unless r represents an operator function or
   operator function template.  */

static tree
eval_operator_of (location_t loc, const constexpr_ctx *ctx, tree r,
		  tree *jump_target, tree ret_type)
{
  if (eval_is_operator_function (r) == boolean_false_node)
    return throw_exception (loc, ctx,
			    N_("reflection does not represent an operator "
			       "function"), r, jump_target);
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);
  r = STRIP_TEMPLATE (r);
  maybe_init_meta_operators (loc);
  int i = IDENTIFIER_ASSIGN_OP_P (DECL_NAME (r)) ? 1 : 0;
  int j = IDENTIFIER_CP_INDEX (DECL_NAME (r));
  return build_int_cst (ret_type, meta_operators[i][j]);
}

/* Process std::meta::{,u8}symbol_of.
   Returns: A string_view or u8string_view containing the characters of the
   operator symbol name corresponding to op, respectively encoded with the
   ordinary literal encoding or with UTF-8.
   Throws: meta::exception unless the value of op corresponds to one of the
   enumerators in operators.  */

static tree
eval_symbol_of (location_t loc, const constexpr_ctx *ctx, tree expr,
		tree *jump_target, tree elt_type, tree ret_type)
{
  maybe_init_meta_operators (loc);
  if (!tree_fits_uhwi_p (expr))
    {
    fail:
      return throw_exception (loc, ctx,
			      N_("operators argument is not a valid operator"),
			      expr, jump_target);
    }
  unsigned HOST_WIDE_INT val = tree_to_uhwi (expr);
  for (int i = 0; i < 2; ++i)
    for (int j = OVL_OP_ERROR_MARK + 1; j < OVL_OP_MAX; ++j)
      if (ovl_op_info[i][j].meta_name && meta_operators[i][j] == val)
	{
	  const char *name = ovl_op_info[i][j].name;
	  char buf[64];
	  if (const char *sp = strchr (name, ' '))
	    {
	      memcpy (buf, name, sp - name);
	      strcpy (buf + (sp - name), sp + 1);
	      name = buf;
	    }
	  tree str = build_string_literal (strlen (name) + 1, name, elt_type);
	  releasing_vec args (make_tree_vector_single (str));
	  tree r = build_special_member_call (NULL_TREE,
					      complete_ctor_identifier,
					      &args, ret_type, LOOKUP_NORMAL,
					      tf_warning_or_error);
	  return build_cplus_new (ret_type, r, tf_warning_or_error);
	}
  goto fail;
}

/* has-type (exposition only).
   Returns: true if r represents a value, annotation, object, variable,
   function whose type does not contain an undeduced placeholder type and
   that is not a constructor or destructor, enumerator, non-static data
   member, unnamed bit-field, direct base class relationship, data member
   description, or function parameter.  Otherwise, false.  */

static bool
has_type (tree r, reflect_kind kind)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL)
    {
      if (DECL_CONSTRUCTOR_P (r) || DECL_DESTRUCTOR_P (r))
	return false;
      if (undeduced_auto_decl (r))
	return false;
      return true;
    }
  if (CONSTANT_CLASS_P (r)
      || eval_is_variable (r, kind) == boolean_true_node
      || eval_is_enumerator (r) == boolean_true_node
      || TREE_CODE (r) == FIELD_DECL
      || eval_is_annotation (r) == boolean_true_node
      || eval_is_function_parameter (r, kind) == boolean_true_node)
    return true;
  // TODO: object, direct base class relationship, data member description.
  return false;
}

/* Helper function for eval_type_of.  Assuming has_type is true, return
   the std::meta::type_of type (rather than reflection thereof).  */

static tree
type_of (tree r, reflect_kind kind)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == PARM_DECL && kind == REFLECT_PARM)
    {
      tree fn = DECL_CONTEXT (r);
      tree args = FUNCTION_FIRST_USER_PARM (fn);
      tree type = FUNCTION_FIRST_USER_PARMTYPE (fn);
      while (r != args)
	{
	  args = DECL_CHAIN (args);
	  type = TREE_CHAIN (type);
	}
      r = TREE_VALUE (type);
    }
  else if (eval_is_annotation (r) == boolean_true_node)
    // TODO: or do we need to reflect_constant and get type of that?
    r = TREE_TYPE (TREE_VALUE (TREE_VALUE (r)));
  else
    r = TREE_TYPE (r);
  return r;
}

/* Process std::meta::type_of.  Returns:
   -- If r represents the ith parameter of a function F, then the ith type
      in the parameter-type-list of F.
   -- Otherwise, if r represents a value, object, variable, function,
      non-static data member, or unnamed bit-field, then the type of what is
      represented by r.
   -- Otherwise, if r represents an annotation, then type_of(constant_of(r)).
   -- Otherwise, if r represents an enumerator N of an enumeration E, then:
      -- If E is defined by a declaration D that precedes a point P in the
	 evaluation context and P does not occur within an enum-specifier of
	 D, then a reflection of E.
      -- Otherwise, a reflection of the type of N prior to the closing brace
	 of the enum-specifier as specified in [dcl.enum].
   -- Otherwise, if r represents a direct base class relationship (D,B), then
      a reflection of B.
   -- Otherwise, for a data member description (T,N,A,W,NUA), a reflection of
      the type T.  */

static tree
eval_type_of (location_t loc, const constexpr_ctx *ctx, tree r,
	      reflect_kind kind, tree *jump_target)
{
  if (!has_type (r, kind))
    return throw_exception (loc, ctx, N_("reflection does not have a type"),
			    r, jump_target);
  return get_reflection_raw (loc, type_of (r, kind));
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
  // TODO what's not an entity?
  else if (0)
    return throw_exception_generic (loc, ctx, r, jump_target);

  return get_reflection_raw (loc, r);
}

/* Process std::meta::is_const.
   Let T be type_of(r) if has-type(r) is true.  Otherwise, let T be dealias(r).
   Returns: true if T represents a const type, or a const-qualified function
   type.  Otherwise, false.  */

static tree
eval_is_const (tree r, reflect_kind kind)
{
  if (has_type (r, kind))
    r = type_of (r, kind);
  else if (TYPE_P (r) && typedef_variant_p (r))
    r = strip_typedefs (r);
  if (TYPE_P (r) && TYPE_READONLY (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_volatile.
   Let T be type_of(r) if has-type(r) is true.  Otherwise, let T be dealias(r).
   Returns: true if T represents a volatile type, or a volatile-qualified
   function type.  Otherwise, false.  */

static tree
eval_is_volatile (tree r, reflect_kind kind)
{
  if (has_type (r, kind))
    r = type_of (r, kind);
  else if (TYPE_P (r) && typedef_variant_p (r))
    r = strip_typedefs (r);
  if (TYPE_P (r) && TYPE_VOLATILE (r))
    return boolean_true_node;
  else
    return boolean_false_node;
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

/* Process std::meta::has_parent
   Returns:
   -- If r represents the global namespace, then false.
   -- Otherwise, if r represents an entity that has C language linkage,
      then false.
   -- Otherwise, if r represents an entity that has a language linkage
      other than C++ language linkage, then an implementation-defined value.
   -- Otherwise, if r represents a type that is neither a class nor enumeration
      type, then false.
   -- Otherwise, if r represents an entity or direct base class relationship,
      then true.
   -- Otherwise, false.  */

static tree
eval_has_parent (tree r, reflect_kind kind)
{
  if (kind == REFLECT_OBJECT || CONSTANT_CLASS_P (r) || r == global_namespace)
    return boolean_false_node;
  if (TYPE_P (r))
    {
      if (TYPE_NAME (r)
	  && DECL_P (TYPE_NAME (r))
	  && DECL_LANGUAGE (TYPE_NAME (r)) == lang_c)
	return boolean_false_node;
      else if (OVERLOAD_TYPE_P (r) || typedef_variant_p (r))
	return boolean_true_node;
      else
	return boolean_false_node;
    }
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);
  // TODO: Handle direct base class relationship and punt on data member
  // description.
  if (!DECL_P (r))
    return boolean_false_node;
  if (TREE_CODE (r) != NAMESPACE_DECL && DECL_LANGUAGE (r) == lang_c)
    return boolean_false_node;
  return boolean_true_node;
}

/* Process std::meta::parent_of.
   Returns:
   -- If r represents a non-static data member that is a direct member of an
      anonymous union, or an unnamed bit-field declared within the
      member-specification of such a union, then a reflection representing the
      innermost enclosing anonymous union.
   -- Otherwise, if r represents an enumerator, then a reflection representing
      the corresponding enumeration type.
   -- Otherwise, if r represents a direct base class relationship (D,B), then
      a reflection representing D.
   -- Otherwise, let E be a class, function, or namespace whose class scope,
      function parameter scope, or namespace scope, respectively, is the
      innermost such scope that either is, or encloses, the target scope of a
      declaration of what is represented by r.
      -- If E is the function call operator of a closure type for a
	 consteval-block-declaration, then parent_of(parent_of(^^E)).
      -- Otherwise, ^^E.  */

static tree
eval_parent_of (location_t loc, const constexpr_ctx *ctx, tree r,
		reflect_kind kind, tree *jump_target)
{
  if (eval_has_parent (r, kind) != boolean_true_node)
    return throw_exception (loc, ctx, N_("reflection does not represent an "
					 "entity with parent"), r,
			    jump_target);
  tree c;
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);
  if (TYPE_P (r))
    {
      if (TYPE_NAME (r) && DECL_P (TYPE_NAME (r)))
	c = CP_DECL_CONTEXT (TYPE_NAME (r));
      else
	c = CP_TYPE_CONTEXT (r);
    }
  else if (VAR_P (r) && DECL_ANON_UNION_VAR_P (r))
    {
      tree v = DECL_VALUE_EXPR (r);
      if (v != error_mark_node && TREE_CODE (v) == COMPONENT_REF)
	c = CP_DECL_CONTEXT (TREE_OPERAND (v, 1));
      else
	c = CP_DECL_CONTEXT (r);
    }
  // TODO: Handle direct base class relationship.
  else
    c = CP_DECL_CONTEXT (r);
  tree lam;
  while (LAMBDA_FUNCTION_P (c)
	 && (lam = CLASSTYPE_LAMBDA_EXPR (CP_DECL_CONTEXT (c)))
	 && LAMBDA_EXPR_CONSTEVAL_BLOCK_P (lam))
    c = CP_TYPE_CONTEXT (CP_DECL_CONTEXT (c));
  return get_reflection_raw (loc, c);
}

/* Build std::vector<info>{ ELTS }.  */

static tree
get_vector_of_info_elts (vec<constructor_elt, va_gc> *elts)
{
  tree ctor = build_constructor (init_list_type_node, elts);
  CONSTRUCTOR_IS_DIRECT_INIT (ctor) = true;
  TREE_CONSTANT (ctor) = true;
  TREE_STATIC (ctor) = true;
  tree type = get_vector_info ();
  if (!type)
    return error_mark_node;
  tree r = finish_compound_literal (type, ctor, tf_warning_or_error,
				    fcl_functional);
  if (TREE_CODE (r) == TARGET_EXPR)
    r = TARGET_EXPR_INITIAL (r);
  return r;
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
  if (eval_is_function (r) != boolean_true_node
      && (eval_is_type (r) != boolean_true_node
	  || eval_is_function_type (loc, ctx, r,
				    jump_target) != boolean_true_node))
    return throw_exception_nofn (loc, ctx, r, jump_target);

  r = MAYBE_BASELINK_FUNCTIONS (r);
  vec<constructor_elt, va_gc> *elts = nullptr;
  tree args = (TREE_CODE (r) == FUNCTION_DECL
	       ? FUNCTION_FIRST_USER_PARM (r)
	       : TYPE_ARG_TYPES (r));
  for (tree arg = args; arg && arg != void_list_node; arg = TREE_CHAIN (arg))
    CONSTRUCTOR_APPEND_ELT (elts, NULL_TREE,
			    get_reflection_raw (location_of (arg), arg,
						REFLECT_PARM));
  return get_vector_of_info_elts (elts);
}

/* Process std::meta::variable_of.
   Returns: The reflection of the parameter variable corresponding to r.

   Throws: meta::exception unless
   -- represents a parameter of a function F and
   -- there is a point P in the evaluation context for which the innermost
      non-block scope enclosing P is the function parameter scope associated
      with F.  */

static tree
eval_variable_of (location_t loc, const constexpr_ctx *ctx, tree r,
		  reflect_kind kind, tree *jump_target)
{
  if (eval_is_function_parameter (r, kind) == boolean_false_node
      || DECL_CONTEXT (r) != current_function_decl)
    return throw_exception (loc, ctx, N_("reflection does not represent "
					 "parameter of current function"),
			    r, jump_target);
  return get_reflection_raw (loc, r, REFLECT_UNDEF);
}

/* Process std::meta::return_type_of.
   Returns: The reflection of the return type of the function or function type
   represented by r.

   Throws: meta::exception unless either r represents a function and
   has-type(r) is true or r represents a function type.  */

static tree
eval_return_type_of (location_t loc, const constexpr_ctx *ctx, tree r,
		     reflect_kind kind, tree *jump_target)
{
  if ((eval_is_function (r) != boolean_true_node || !has_type (r, kind))
      && (eval_is_type (r) != boolean_true_node
	  || eval_is_function_type (loc, ctx, r,
				    jump_target) != boolean_true_node))
    return throw_exception_nofn (loc, ctx, r, jump_target);

  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == FUNCTION_DECL)
    r = TREE_TYPE (r);
  r = TREE_TYPE (r);
  return get_reflection_raw (loc, r, REFLECT_UNDEF);
}

/* Process std::meta::offset_of.
   Let V be the offset in bits from the beginning of a complete object of the
   type represented by parent_of(r) to the subobject associated with the
   entity represented by r.
   Returns: {V / CHAR_BIT, V % CHAR_BIT}.
   Throws: meta::exception unless r represents a non-static data member,
   unnamed bit-field, or direct base class relationship (D,B) for which either
   B is not a virtual base class or D is not an abstract class.  */

static tree
eval_offset_of (location_t loc, const constexpr_ctx *ctx, tree r,
		tree member_offset, tree *jump_target)
{
  if (TREE_CODE (r) != FIELD_DECL
      /* TODO: Handle direct base class relationship.  */)
    return throw_exception (loc, ctx,
			    N_("reflection unsuitable for offset"),
			    r, jump_target);
  tree off = bit_position (r);
  if (TREE_CODE (off) != INTEGER_CST)
    return throw_exception (loc, ctx,
			    N_("non-constant offset for offset_of"),
			    r, jump_target);
  if (TREE_CODE (member_offset) != RECORD_TYPE)
    {
    fail:
      error_at (loc, "unexpected return type of %qs", "std::meta::offset_of");
      return build_zero_cst (member_offset);
    }
  tree bytes = next_aggregate_field (TYPE_FIELDS (member_offset));
  if (!bytes || !INTEGRAL_TYPE_P (TREE_TYPE (bytes)))
    goto fail;
  tree bits = next_aggregate_field (DECL_CHAIN (bytes));
  if (!bits || !INTEGRAL_TYPE_P (TREE_TYPE (bits)))
    goto fail;
  if (next_aggregate_field (DECL_CHAIN (bits)))
    goto fail;
  tree bytesv = size_binop (TRUNC_DIV_EXPR, off, bitsize_unit_node);
  bytesv = fold_convert (TREE_TYPE (bytes), bytesv);
  tree bitsv = size_binop (TRUNC_MOD_EXPR, off, bitsize_unit_node);
  bitsv = fold_convert (TREE_TYPE (bits), bitsv);
  vec<constructor_elt, va_gc> *elts = nullptr;
  CONSTRUCTOR_APPEND_ELT (elts, bytes, bytesv);
  CONSTRUCTOR_APPEND_ELT (elts, bits, bitsv);
  return build_constructor (member_offset, elts);
}

/* Process std::meta::size_of.
   Returns: If r represents
     -- a non-static data member of type T,
     -- a data member description (T,N,A,W,NUA), or
     -- dealias(r) represents a type T,
   then sizeof(T) if T is not a reference type and size_of(add_pointer(^^T))
   otherwise.  Otherwise, size_of(type_of(r)).

   Throws: meta::exception unless all of the following conditions are met:
     -- dealias(r) is a reflection of a type, object, value, variable of
	non-reference type, non-static data member that is not a bit-field,
	direct base class relationship, or data member description
	(T,N,A,W,NUA) where W is not _|_.
     -- If dealias(r) represents a type, then is_complete_type(r) is true.  */

static tree
eval_size_of (location_t loc, const constexpr_ctx *ctx, tree r,
	      reflect_kind kind, tree ret_type, tree *jump_target)
{
  if (eval_is_type (r) != boolean_true_node
      && eval_is_object (kind) != boolean_true_node
      /* TODO: value */
      && (eval_is_variable (r, kind) != boolean_true_node
	  || TYPE_REF_P (TREE_TYPE (r)))
      && (TREE_CODE (r) != FIELD_DECL || DECL_C_BIT_FIELD (r))
      /* TODO: direct base class relationship, data member description.  */)
    return throw_exception (loc, ctx,
			    N_("reflection not suitable for size_of"),
			    r, jump_target);
  if (!INTEGRAL_TYPE_P (ret_type))
    {
      error_at (loc, "unexpected return type of %qs", "std::meta::size_of");
      return build_zero_cst (ret_type);
    }
  tree type;
  if (TYPE_P (r))
    type = r;
  else if (TREE_CODE (r) == FIELD_DECL)
    type = TREE_TYPE (r);
  else
    type = type_of (r, kind);
  if (type == error_mark_node || !COMPLETE_TYPE_P (type))
    return throw_exception (loc, ctx,
			    N_("reflection with incomplete type"),
			    r, jump_target);
  tree ret = c_sizeof_or_alignof_type (loc, type, true, false, 0);
  if (ret == error_mark_node)
    return throw_exception (loc, ctx,
			    N_("reflection with incomplete type"),
			    r, jump_target);
  return fold_convert (ret_type, ret);
}

/* Process std::meta::bit_size_of.
   Returns:
     -- If r represents an unnamed bit-field or a non-static data member that
	is a bit-field with width W, then W.
     -- Otherwise, if r represents a data member description (T,N,A,W,NUA)
	and W is not _|_, then W.
     -- Otherwise, CHAR_BIT * size_of(r).

   Throws: meta::exception unless all of the following conditions are met:

     -- dealias(r) is a reflection of a type, object, value, variable of
	non-reference type, non-static data member, unnamed bit-field, direct
	base class relationship, or data member description.
     -- If dealias(r) represents a type T, there is a point within the
	evaluation context from which T is not incomplete.  */

static tree
eval_bit_size_of (location_t loc, const constexpr_ctx *ctx, tree r,
		  reflect_kind kind, tree ret_type, tree *jump_target)
{
  if (eval_is_type (r) != boolean_true_node
      && eval_is_object (kind) != boolean_true_node
      /* TODO: value */
      && (eval_is_variable (r, kind) != boolean_true_node
	  || TYPE_REF_P (TREE_TYPE (r)))
      && TREE_CODE (r) != FIELD_DECL
      /* TODO: direct base class relationship, data member description.  */)
    return throw_exception (loc, ctx,
			    N_("reflection not suitable for bit_size_of"),
			    r, jump_target);
  if (!INTEGRAL_TYPE_P (ret_type))
    {
      error_at (loc, "unexpected return type of %qs",
		"std::meta::bit_size_of");
      return build_zero_cst (ret_type);
    }
  tree type;
  if (TREE_CODE (r) == FIELD_DECL && DECL_C_BIT_FIELD (r))
    return fold_convert (ret_type, DECL_SIZE (r));
  else if (TYPE_P (r))
    type = r;
  else if (TREE_CODE (r) == FIELD_DECL)
    type = TREE_TYPE (r);
  else
    type = type_of (r, kind);
  if (type == error_mark_node || !COMPLETE_TYPE_P (type))
    return throw_exception (loc, ctx,
			    N_("reflection with incomplete type"),
			    r, jump_target);
  tree ret = c_sizeof_or_alignof_type (loc, type, true, false, 0);
  if (ret == error_mark_node)
    return throw_exception (loc, ctx,
			    N_("reflection with incomplete type"),
			    r, jump_target);
  ret = size_binop (MULT_EXPR, ret, size_int (BITS_PER_UNIT));
  return fold_convert (ret_type, ret);
}

/* Get the reflection of template argument ARG as per
   std::meta::template_arguments_of.  */

static tree
get_reflection_of_targ (tree arg)
{
  const location_t loc = location_of (arg);
  /* canonicalize_type_argument already strip_typedefs.  */
  arg = STRIP_REFERENCE_REF (arg);
  return get_reflection_raw (loc, arg);
}

/* Process std::meta::template_arguments_of.
   Returns: A vector containing reflections of the template arguments of the
   template specialization represented by r, in the order in which they appear
   in the corresponding template argument list.
   For a given template argument A, its corresponding reflection R is
   determined as follows:

   -- If A denotes a type or type alias, then R is a reflection representing
      the underlying entity of A.
   -- Otherwise, if A denotes a class template, variable template, concept,
      or alias template, then R is a reflection representing A.
   -- Otherwise, A is a constant template argument.  Let P be the
      corresponding template parameter.
      -- If P has reference type, then R is a reflection representing the
	 object or function referred to by A.
      -- Otherwise, if P has class type, then R represents the corresponding
	 template parameter object.
      -- Otherwise, R is a reflection representing the value of A.

   Throws: meta::exception unless has_template_arguments(r) is true.  */

static tree
eval_template_arguments_of (location_t loc, const constexpr_ctx *ctx, tree r,
			    tree *jump_target)
{
  if (eval_has_template_arguments (r) != boolean_true_node)
    return throw_exception_notargs (loc, ctx, r, jump_target);

  vec<constructor_elt, va_gc> *elts = nullptr;
  tree args = NULL_TREE;
  if (TYPE_P (r) && typedef_variant_p (r))
    {
      if (tree tinfo = TYPE_ALIAS_TEMPLATE_INFO (r))
	args = INNERMOST_TEMPLATE_ARGS (TI_ARGS (tinfo));
    }
  else
    args = get_template_innermost_arguments (r);
  gcc_assert (args);
  for (tree arg : tree_vec_range (args))
    {
      if (ARGUMENT_PACK_P (arg))
	{
	  tree pargs = ARGUMENT_PACK_ARGS (arg);
	  for (tree a : tree_vec_range (pargs))
	    CONSTRUCTOR_APPEND_ELT (elts, NULL_TREE,
				    get_reflection_of_targ (a));
	}
      else
	CONSTRUCTOR_APPEND_ELT (elts, NULL_TREE, get_reflection_of_targ (arg));
    }
  return get_vector_of_info_elts (elts);
}

/* Helper for eval_remove_const to build non-const type.  */

static tree
remove_const (tree type)
{
  return cp_build_qualified_type (type,
				  cp_type_quals (type) & ~TYPE_QUAL_CONST);
}

/* Process std::meta::annotations_of and annotations_of_with_type.
   Let E be
   -- the corresponding base-specifier if item represents a direct base class
      relationship,
   -- otherwise, the entity represented by item.
   Returns: A vector containing all of the reflections R representing each
   annotation applying to each declaration of E that precedes either some
   point in the evaluation context or a point immediately following the
   class-specifier of the outermost class for which such a point is in a
   complete-class context.
   For any two reflections R1 and R2 in the returned vector, if the annotation
   represented by R1 precedes the annotation represented by R2, then R1
   appears before R2.
   If R1 and R2 represent annotations from the same translation unit T, any
   element in the returned vector between R1 and R2 represents an annotation
   from T.

   Throws: meta::exception unless item represents a type, type alias,
   variable, function, namespace, enumerator, direct base class relationship,
   or non-static data member.  */

static tree
eval_annotations_of (location_t loc, const constexpr_ctx *ctx, tree r,
		     reflect_kind kind, tree type, tree *jump_target)
{
  if (!(eval_is_type (r) == boolean_true_node
	|| eval_is_type_alias (r) == boolean_true_node
	|| eval_is_variable (r, kind) == boolean_true_node
	|| eval_is_function (r) == boolean_true_node
	|| eval_is_namespace (r) == boolean_true_node
	|| eval_is_enumerator (r) == boolean_true_node
	/* || eval_is_base (r) == boolean_true_node */
	/* || eval_is_nonstatic_data_member (r) == boolean_true_node */))
    return throw_exception (loc, ctx,
			    N_("reflection does not represent a type,"
			       " type alias, variable, function, namespace,"
			       " enumerator, direct base class relationship,"
			       " or non-static data member"),
			    r, jump_target);

  if (type)
    {
      if (TYPE_P (type) && typedef_variant_p (type))
	type = strip_typedefs (type);
      if (!TYPE_P (type) || !COMPLETE_TYPE_P (type))
	return throw_exception (loc, ctx,
				N_("reflection does not represent a complete"
				   " type or type alias"),
				type, jump_target);
      type = remove_const (type);
    }

  if (TYPE_P (r))
    r = TYPE_ATTRIBUTES (r);
  else if (DECL_P (r))
    r = DECL_ATTRIBUTES (r);
  else
    gcc_unreachable (); // TODO: Handle eval_is_base?
  vec<constructor_elt, va_gc> *elts = nullptr;
  for (tree a = r; (a = lookup_attribute ("internal ", "annotation ", a));
       a = TREE_CHAIN (a))
    {
      gcc_checking_assert (TREE_CODE (TREE_VALUE (a)) == TREE_LIST);
      tree val = TREE_VALUE (TREE_VALUE (a));
      if (type)
	{
	  tree at = TREE_TYPE (val);
	  if (at == error_mark_node)
	    continue;
	  if (at != type && !same_type_p (remove_const (at), type))
	    continue;
	}
      CONSTRUCTOR_APPEND_ELT (elts, NULL_TREE,
			      get_reflection_raw (location_of (val), a));
    }
  return get_vector_of_info_elts (elts);
}

/* Process std::meta::reflect_constant.
   Mandates: is_copy_constructible_v<T> is true and T is a cv-unqualified
   structural type that is not a reference type.
   Let V be:
   -- if T is a class type, then an object that is template-argument-equivalent
      to the value of expr;
   -- otherwise, the value of expr.
   Returns: template_arguments_of(^^TCls<V>)[0], with TCls as defined below.
   Throws: meta::exception unless the template-id TCls<V> would be valid given
   the invented template
     template<T P> struct TCls;  */

static tree
eval_reflect_constant (location_t loc, const constexpr_ctx *ctx, tree expr,
		       tree *jump_target)
{
  tree type = TREE_TYPE (expr);
  if (!structural_type_p (type)
      || CP_TYPE_VOLATILE_P (type)
      || CP_TYPE_CONST_P (type)
      || TYPE_REF_P (type))
    {
      error_at (loc, "%qT must be a cv-unqualified structural type that is "
		"not a reference type", type);
      return error_mark_node;
    }
  expr = convert_reflect_constant_arg (type, expr);
  if (expr == error_mark_node)
    throw_exception_generic (loc, ctx, type, jump_target);
  return get_reflection_raw (loc, expr);
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

/* Process std::meta::is_arithmetic_type.  */

static tree
eval_is_arithmetic_type (location_t loc, const constexpr_ctx *ctx, tree type,
			 tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (ARITHMETIC_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_object_type.  */

static tree
eval_is_object_type (location_t loc, const constexpr_ctx *ctx, tree type,
		     tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_OBJECT, jump_target);
}

/* Process std::meta::is_scalar_type.  */

static tree
eval_is_scalar_type (location_t loc, const constexpr_ctx *ctx, tree type,
		     tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (SCALAR_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_fundamental_type.  */

static tree
eval_is_fundamental_type (location_t loc, const constexpr_ctx *ctx, tree type,
			  tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (ARITHMETIC_TYPE_P (type)
      || VOID_TYPE_P (type)
      || NULLPTR_TYPE_P (type)
      || REFLECTION_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_compound_type.  */

static tree
eval_is_compound_type (location_t loc, const constexpr_ctx *ctx, tree type,
		       tree *jump_target)
{
  tree fundamental = eval_is_fundamental_type (loc, ctx, type, jump_target);
  if (fundamental == boolean_false_node)
    return boolean_true_node;
  else if (fundamental == boolean_true_node)
    return boolean_false_node;
  else
    return fundamental;
}

/* Process std::meta::is_member_pointer_type.  */

static tree
eval_is_member_pointer_type (location_t loc, const constexpr_ctx *ctx,
			     tree type, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_MEMBER_POINTER, jump_target);
}

/* Process std::meta::is_const_type.  */

static tree
eval_is_const_type (location_t loc, const constexpr_ctx *ctx, tree type,
		    tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (CP_TYPE_CONST_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_volatile_type.  */

static tree
eval_is_volatile_type (location_t loc, const constexpr_ctx *ctx, tree type,
		       tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (CP_TYPE_VOLATILE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_trivially_copyable_type.  */

static tree
eval_is_trivially_copyable_type (location_t loc, const constexpr_ctx *ctx,
				 tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (trivially_copyable_p (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_trivially_relocatable_type.  */

static tree
eval_is_trivially_relocatable_type (location_t loc, const constexpr_ctx *ctx,
				    tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (trivially_relocatable_type_p (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_replaceable_type.  */

static tree
eval_is_replaceable_type (location_t loc, const constexpr_ctx *ctx,
			  tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (replaceable_type_p (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_standard_layout_type.  */

static tree
eval_is_standard_layout_type (location_t loc, const constexpr_ctx *ctx,
			      tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (std_layout_type_p (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_empty_type.  */

static tree
eval_is_empty_type (location_t loc, const constexpr_ctx *ctx, tree type,
		    tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_EMPTY, jump_target);
}

/* Process std::meta::is_polymorphic_type.  */

static tree
eval_is_polymorphic_type (location_t loc, const constexpr_ctx *ctx, tree type,
			  tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_POLYMORPHIC, jump_target);
}

/* Process std::meta::is_abstract_type.  */

static tree
eval_is_abstract_type (location_t loc, const constexpr_ctx *ctx, tree type,
		       tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (ABSTRACT_CLASS_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_final_type.  */

static tree
eval_is_final_type (location_t loc, const constexpr_ctx *ctx, tree type,
		    tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_FINAL, jump_target);
}

/* Process std::meta::is_aggregate_type.  */

static tree
eval_is_aggregate_type (location_t loc, const constexpr_ctx *ctx, tree type,
			tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (CP_AGGREGATE_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_consteval_only_type.  */

static tree
eval_is_consteval_only_type (location_t loc, const constexpr_ctx *ctx,
			     tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (consteval_only_p (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_signed_type.  */

static tree
eval_is_signed_type (location_t loc, const constexpr_ctx *ctx, tree type,
		     tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (ARITHMETIC_TYPE_P (type) && !TYPE_UNSIGNED (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_unsigned_type.  */

static tree
eval_is_unsigned_type (location_t loc, const constexpr_ctx *ctx, tree type,
		       tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (ARITHMETIC_TYPE_P (type) && TYPE_UNSIGNED (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_bounded_array_type.  */

static tree
eval_is_bounded_array_type (location_t loc, const constexpr_ctx *ctx,
			    tree type, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_BOUNDED_ARRAY, jump_target);
}

/* Process std::meta::is_unbounded_array_type.  */

static tree
eval_is_unbounded_array_type (location_t loc, const constexpr_ctx *ctx,
			      tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (array_of_unknown_bound_p (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_scoped_enum_type.  */

static tree
eval_is_scoped_enum_type (location_t loc, const constexpr_ctx *ctx,
			  tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (SCOPED_ENUM_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_default_constructible_type.  */

static tree
eval_is_default_constructible_type (location_t loc, const constexpr_ctx *ctx,
				    tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (is_xible (INIT_EXPR, type, make_tree_vec (0)))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_copy_constructible_type.  */

static tree
eval_is_copy_constructible_type (location_t loc, const constexpr_ctx *ctx,
				 tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree arg = make_tree_vec (1);
  tree ctype
    = cp_build_qualified_type (type, cp_type_quals (type) | TYPE_QUAL_CONST);
  TREE_VEC_ELT (arg, 0) = cp_build_reference_type (ctype, /*rval=*/false);
  if (is_xible (INIT_EXPR, type, arg))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_move_constructible_type.  */

static tree
eval_is_move_constructible_type (location_t loc, const constexpr_ctx *ctx,
				 tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree arg = make_tree_vec (1);
  TREE_VEC_ELT (arg, 0) = cp_build_reference_type (type, /*rval=*/true);
  if (is_xible (INIT_EXPR, type, arg))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_assignable_type.  */

static tree
eval_is_assignable_type (location_t loc, const constexpr_ctx *ctx, tree type1,
			 tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2, CPTK_IS_ASSIGNABLE,
			  jump_target);
}

/* Process std::meta::is_copy_assignable_type.  */

static tree
eval_is_copy_assignable_type (location_t loc, const constexpr_ctx *ctx,
			      tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree type1 = cp_build_reference_type (type, /*rval=*/false);
  tree type2
    = cp_build_qualified_type (type, cp_type_quals (type) | TYPE_QUAL_CONST);
  type2 = cp_build_reference_type (type2, /*rval=*/false);
  if (is_xible (MODIFY_EXPR, type1, type2))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_move_assignable_type.  */

static tree
eval_is_move_assignable_type (location_t loc, const constexpr_ctx *ctx,
			      tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree type1 = cp_build_reference_type (type, /*rval=*/false);
  tree type2 = cp_build_reference_type (type, /*rval=*/true);
  if (is_xible (MODIFY_EXPR, type1, type2))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_destructible_type.  */

static tree
eval_is_destructible_type (location_t loc, const constexpr_ctx *ctx, tree type,
			   tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_DESTRUCTIBLE, jump_target);
}

/* Process std::meta::is_trivially_default_constructible_type.  */

static tree
eval_is_trivially_default_constructible_type (location_t loc,
					      const constexpr_ctx *ctx,
					      tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (is_trivially_xible (INIT_EXPR, type, make_tree_vec (0)))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_trivially_copy_constructible_type.  */

static tree
eval_is_trivially_copy_constructible_type (location_t loc,
					   const constexpr_ctx *ctx, tree type,
					   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree arg = make_tree_vec (1);
  tree ctype
    = cp_build_qualified_type (type, cp_type_quals (type) | TYPE_QUAL_CONST);
  TREE_VEC_ELT (arg, 0) = cp_build_reference_type (ctype, /*rval=*/false);
  if (is_trivially_xible (INIT_EXPR, type, arg))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_trivially_move_constructible_type.  */

static tree
eval_is_trivially_move_constructible_type (location_t loc,
					   const constexpr_ctx *ctx, tree type,
					   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree arg = make_tree_vec (1);
  TREE_VEC_ELT (arg, 0) = cp_build_reference_type (type, /*rval=*/true);
  if (is_trivially_xible (INIT_EXPR, type, arg))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_trivially_assignable_type.  */

static tree
eval_is_trivially_assignable_type (location_t loc, const constexpr_ctx *ctx,
				   tree type1, tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2, CPTK_IS_TRIVIALLY_ASSIGNABLE,
			  jump_target);
}

/* Process std::meta::is_trivially_copy_assignable_type.  */

static tree
eval_is_trivially_copy_assignable_type (location_t loc,
					const constexpr_ctx *ctx, tree type,
					tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree type1 = cp_build_reference_type (type, /*rval=*/false);
  tree type2
    = cp_build_qualified_type (type, cp_type_quals (type) | TYPE_QUAL_CONST);
  type2 = cp_build_reference_type (type2, /*rval=*/false);
  if (is_trivially_xible (MODIFY_EXPR, type1, type2))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_trivially_move_assignable_type.  */

static tree
eval_is_trivially_move_assignable_type (location_t loc,
					const constexpr_ctx *ctx, tree type,
					tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree type1 = cp_build_reference_type (type, /*rval=*/false);
  tree type2 = cp_build_reference_type (type, /*rval=*/true);
  if (is_trivially_xible (MODIFY_EXPR, type1, type2))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_trivially_destructible_type.  */

static tree
eval_is_trivially_destructible_type (location_t loc, const constexpr_ctx *ctx,
				     tree type, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_TRIVIALLY_DESTRUCTIBLE,
			  jump_target);
}

/* Process std::meta::is_nothrow_default_constructible_type.  */

static tree
eval_is_nothrow_default_constructible_type (location_t loc,
					    const constexpr_ctx *ctx,
					    tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (is_nothrow_xible (INIT_EXPR, type, make_tree_vec (0)))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_nothrow_copy_constructible_type.  */

static tree
eval_is_nothrow_copy_constructible_type (location_t loc,
					 const constexpr_ctx *ctx, tree type,
					 tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree arg = make_tree_vec (1);
  tree ctype
    = cp_build_qualified_type (type, cp_type_quals (type) | TYPE_QUAL_CONST);
  TREE_VEC_ELT (arg, 0) = cp_build_reference_type (ctype, /*rval=*/false);
  if (is_nothrow_xible (INIT_EXPR, type, arg))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_nothrow_move_constructible_type.  */

static tree
eval_is_nothrow_move_constructible_type (location_t loc,
					 const constexpr_ctx *ctx, tree type,
					 tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree arg = make_tree_vec (1);
  TREE_VEC_ELT (arg, 0) = cp_build_reference_type (type, /*rval=*/true);
  if (is_nothrow_xible (INIT_EXPR, type, arg))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_nothrow_assignable_type.  */

static tree
eval_is_nothrow_assignable_type (location_t loc, const constexpr_ctx *ctx,
				 tree type1, tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2, CPTK_IS_NOTHROW_ASSIGNABLE,
			  jump_target);
}

/* Process std::meta::is_nothrow_copy_assignable_type.  */

static tree
eval_is_nothrow_copy_assignable_type (location_t loc,
				      const constexpr_ctx *ctx, tree type,
				      tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree type1 = cp_build_reference_type (type, /*rval=*/false);
  tree type2
    = cp_build_qualified_type (type, cp_type_quals (type) | TYPE_QUAL_CONST);
  type2 = cp_build_reference_type (type2, /*rval=*/false);
  if (is_nothrow_xible (MODIFY_EXPR, type1, type2))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_nothrow_move_assignable_type.  */

static tree
eval_is_nothrow_move_assignable_type (location_t loc, const constexpr_ctx *ctx,
				      tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree type1 = cp_build_reference_type (type, /*rval=*/false);
  tree type2 = cp_build_reference_type (type, /*rval=*/true);
  if (is_nothrow_xible (MODIFY_EXPR, type1, type2))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_nothrow_destructible_type.  */

static tree
eval_is_nothrow_destructible_type (location_t loc, const constexpr_ctx *ctx,
				   tree type, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_NOTHROW_DESTRUCTIBLE,
			  jump_target);
}

/* Process std::meta::is_nothrow_relocatable_type.  */

static tree
eval_is_nothrow_relocatable_type (location_t loc, const constexpr_ctx *ctx,
				  tree type, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type, CPTK_IS_NOTHROW_RELOCATABLE,
			  jump_target);
}

/* Process std::meta::has_virtual_destructor.  */

static tree
eval_has_virtual_destructor (location_t loc, const constexpr_ctx *ctx,
			     tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (type_has_virtual_destructor (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_unique_object_representations.  */

static tree
eval_has_unique_object_representations (location_t loc,
					const constexpr_ctx *ctx, tree type,
					tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (type_has_unique_obj_representations (type))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::reference_constructs_from_temporary.  */

static tree
eval_reference_constructs_from_temporary (location_t loc,
					  const constexpr_ctx *ctx, tree type1,
					  tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2,
			  CPTK_REF_CONSTRUCTS_FROM_TEMPORARY, jump_target);
}

/* Process std::meta::reference_converts_from_temporary.  */

static tree
eval_reference_converts_from_temporary (location_t loc,
					const constexpr_ctx *ctx, tree type1,
					tree type2, tree *jump_target)
{
  return eval_type_trait (loc, ctx, type1, type2,
			  CPTK_REF_CONVERTS_FROM_TEMPORARY, jump_target);
}

/* Process std::meta::rank.  */

static tree
eval_rank (location_t loc, const constexpr_ctx *ctx, tree type,
	   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  size_t rank = 0;
  for (; TREE_CODE (type) == ARRAY_TYPE; type = TREE_TYPE (type))
    ++rank;
  return build_int_cst (size_type_node, rank);
}

/* Process std::meta::extent.  */

static tree
eval_extent (location_t loc, const constexpr_ctx *ctx, tree type,
	     tree i, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  size_t rank = tree_to_uhwi (i);
  while (rank && TREE_CODE (type) == ARRAY_TYPE)
    {
      --rank;
      type = TREE_TYPE (type);
    }
  if (rank
      || TREE_CODE (type) != ARRAY_TYPE
      || eval_is_bounded_array_type (loc, ctx, type,
				     jump_target) == boolean_false_node)
     return size_zero_node;
  return size_binop (PLUS_EXPR, TYPE_MAX_VALUE (TYPE_DOMAIN (type)),
		     size_one_node);
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

/* Process std::meta::enumerators_of.
   Returns: A vector containing the reflections of each enumerator of the
   enumeration represented by dealias(type_enum), in the order in which they
   are declared.
   Throws: meta::exception unless dealias(type_enum) represents an enumeration
   type, and is_enumerable_type(type_enum) is true.  */

static tree
eval_enumerators_of (location_t loc, const constexpr_ctx *ctx, tree r,
		     tree *jump_target)
{
  if (TREE_CODE (r) != ENUMERAL_TYPE
      || eval_is_enumerable_type (r) == boolean_false_node)
    return throw_exception (loc, ctx, N_("reflection does not represent an "
					 "enumerable enumeration type"), r,
			    jump_target);
  vec<constructor_elt, va_gc> *elts = nullptr;
  for (tree t = TYPE_VALUES (r); t; t = TREE_CHAIN (t))
    {
      tree e = TREE_VALUE (t);
      CONSTRUCTOR_APPEND_ELT (elts, NULL_TREE,
			      get_reflection_raw (location_of (e), e));
    }
  return get_vector_of_info_elts (elts);
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
  return get_reflection_raw (loc, strip_typedefs (remove_const (type)));
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
  type = strip_typedefs (type);
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
  type = strip_typedefs (type);
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
  if (!TYPE_REF_P (type) && !FUNC_OR_METHOD_TYPE_P (type))
    {
      int quals = cp_type_quals (type);
      quals |= TYPE_QUAL_CONST;
      type = cp_build_qualified_type (type, quals);
    }
  type = strip_typedefs (type);
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
  if (!TYPE_REF_P (type) && !FUNC_OR_METHOD_TYPE_P (type))
    {
      int quals = cp_type_quals (type);
      quals |= TYPE_QUAL_VOLATILE;
      type = cp_build_qualified_type (type, quals);
    }
  type = strip_typedefs (type);
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
  if (!TYPE_REF_P (type) && !FUNC_OR_METHOD_TYPE_P (type))
    {
      int quals = cp_type_quals (type);
      quals |= (TYPE_QUAL_CONST | TYPE_QUAL_VOLATILE);
      type = cp_build_qualified_type (type, quals);
    }
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::remove_reference.
   Returns: a reflection representing the type denoted by
   std::remove_reference_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_remove_reference (location_t loc, const constexpr_ctx *ctx, tree type,
		       tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (TYPE_REF_P (type))
    type = TREE_TYPE (type);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::add_lvalue_reference.
   Returns: a reflection representing the type denoted by
   std::add_lvalue_reference_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_add_lvalue_reference (location_t loc, const constexpr_ctx *ctx, tree type,
			   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = finish_trait_type (CPTK_ADD_LVALUE_REFERENCE, type, NULL_TREE, tf_none);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::add_rvalue_reference.
   Returns: a reflection representing the type denoted by
   std::add_rvalue_reference_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_add_rvalue_reference (location_t loc, const constexpr_ctx *ctx, tree type,
			   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = finish_trait_type (CPTK_ADD_RVALUE_REFERENCE, type, NULL_TREE, tf_none);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::make_signed and std::meta::make_unsigned.
   Returns: a reflection representing the type denoted by
   std::make_signed_t<T> or std::make_unsigned_t<T>, respectively, where T is
   the type or type alias represented by type.  */

static tree
eval_make_signed (location_t loc, const constexpr_ctx *ctx, tree type,
		  bool unsignedp, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  // TODO: I don't see the standard specifying what to do here.
  if (!INTEGRAL_TYPE_P (type) || TREE_CODE (type) == BOOLEAN_TYPE)
    return throw_exception (loc, ctx, N_("reflection represents non-integral "
					 "or bool type"), type, jump_target);
  tree ret = type;
  if (TREE_CODE (type) == ENUMERAL_TYPE
      || TYPE_MAIN_VARIANT (type) == wchar_type_node
      || TYPE_MAIN_VARIANT (type) == char8_type_node
      || TYPE_MAIN_VARIANT (type) == char16_type_node
      || TYPE_MAIN_VARIANT (type) == char32_type_node)
    {
      tree unit = TYPE_SIZE_UNIT (type);
      tree types[] = {
	signed_char_type_node,
	short_integer_type_node,
	integer_type_node,
	long_integer_type_node,
	long_long_integer_type_node };
      ret = NULL_TREE;
      for (unsigned i = 0; i < ARRAY_SIZE (types); ++i)
	if (tree_int_cst_equal (TYPE_SIZE_UNIT (types[i]), unit))
	  {
	    ret = c_common_signed_or_unsigned_type (unsignedp, types[i]);
	    break;
	  }
      if (!ret)
	ret = c_common_type_for_size (TYPE_PRECISION (type), unsignedp);
    }
  else if (TYPE_MAIN_VARIANT (type) == char_type_node)
    ret = unsignedp ? unsigned_char_type_node : signed_char_type_node;
  else if (unsignedp ^ (!!TYPE_UNSIGNED (type)))
    ret = c_common_signed_or_unsigned_type (unsignedp, type);
  if (ret != type)
    {
      int quals = cp_type_quals (type);
      quals &= (TYPE_QUAL_CONST | TYPE_QUAL_VOLATILE);
      ret = cp_build_qualified_type (ret, quals);
    }
  else
    ret = strip_typedefs (type);
  return get_reflection_raw (loc, ret);
}

/* Process std::meta::remove_extent.
   Returns: a reflection representing the type denoted by
   std::remove_extent_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_remove_extent (location_t loc, const constexpr_ctx *ctx, tree type,
		    tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (TREE_CODE (type) == ARRAY_TYPE)
    type = TREE_TYPE (type);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::remove_all_extents.
   Returns: a reflection representing the type denoted by
   std::remove_all_extents_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_remove_all_extents (location_t loc, const constexpr_ctx *ctx, tree type,
			 tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = strip_array_types (type);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::remove_pointer.
   Returns: a reflection representing the type denoted by
   std::remove_pointer_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_remove_pointer (location_t loc, const constexpr_ctx *ctx, tree type,
		     tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (TYPE_PTR_P (type))
    type = TREE_TYPE (type);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::add_pointer.
   Returns: a reflection representing the type denoted by
   std::add_pointer_t<T>, where T is the type or type alias
   represented by type.  */

static tree
eval_add_pointer (location_t loc, const constexpr_ctx *ctx, tree type,
		  tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = finish_trait_type (CPTK_ADD_POINTER, type, NULL_TREE, tf_none);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Expand a call to a metafunction.  CALL is the CALL_EXPR.
   JUMP_TARGET is set if we are throwing std::meta::exception.  */

// TODO Use gperf?
tree
process_metafunction (const constexpr_ctx *ctx, tree call,
		      bool *non_constant_p, bool *overflow_p,
		      tree *jump_target)
{
  tree name = DECL_NAME (cp_get_callee_fndecl_nofold (call));
  const char *ident = IDENTIFIER_POINTER (name);

  if (id_equal (name, "reflect_constant"))
    {
      tree expr = get_nth_callarg (call, 0);
      location_t loc = cp_expr_loc_or_input_loc (expr);
      expr = cxx_eval_constant_expression (ctx, expr, vc_prvalue,
					   non_constant_p, overflow_p,
					   jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      return eval_reflect_constant (loc, ctx, expr, jump_target);
    }
  if (id_equal (name, "symbol_of") || id_equal (name, "u8symbol_of"))
    {
      tree expr = get_nth_callarg (call, 0);
      location_t loc = cp_expr_loc_or_input_loc (expr);
      expr = cxx_eval_constant_expression (ctx, expr, vc_prvalue,
					   non_constant_p, overflow_p,
					   jump_target);
      if (*jump_target)
	return NULL_TREE;
      return eval_symbol_of (loc, ctx, expr, jump_target,
			     id_equal (name, "symbol_of") ? char_type_node
			     : char8_type_node, TREE_TYPE (call));
    }

  tree info = get_info (ctx, call, 0, non_constant_p, overflow_p, jump_target);
  if (*jump_target)
    return NULL_TREE;
  if (*non_constant_p)
    return call;
  tree h = REFLECT_EXPR_HANDLE (info);
  auto kind = static_cast<reflect_kind>(REFLECT_EXPR_KIND (info));
  const location_t loc = cp_expr_loc_or_input_loc (info);

  /* There still could be a TEMPLATE_ID_EXPR denoting a function template.  */
  h = resolve_nondeduced_context (h, tf_warning_or_error);

  /* Handle is_*.  */
  if (startswith (ident, "is_"))
    {
      ident += 3;
      if (!strcmp (ident, "variable"))
	return eval_is_variable (h, kind);
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
      if (!strcmp (ident, "object"))
	return eval_is_object (kind);
      if (!strcmp (ident, "structured_binding"))
	return eval_is_structured_binding (h);
      if (!strcmp (ident, "template"))
	return eval_is_template (h);
      if (!strcmp (ident, "function_parameter"))
	return eval_is_function_parameter (h, kind);
      if (!strcmp (ident, "explicit_object_parameter"))
	return eval_is_explicit_object_parameter (h, kind);
      if (!strcmp (ident, "enumerator"))
	return eval_is_enumerator (h);
      if (!strcmp (ident, "complete_type"))
	return eval_is_complete_type (h);
      if (!strcmp (ident, "enumerable_type"))
	return eval_is_enumerable_type (h);
      if (!strcmp (ident, "annotation"))
	return eval_is_annotation (h);
      if (!strcmp (ident, "const"))
	return eval_is_const (h, kind);
      if (!strcmp (ident, "volatile"))
	return eval_is_volatile (h, kind);
      if (!strcmp (ident, "conversion_function"))
	return eval_is_conversion_function (h);
      if (!strcmp (ident, "operator_function"))
	return eval_is_operator_function (h);
      if (!strcmp (ident, "literal_operator"))
	return eval_is_literal_operator (h);
      if (!strcmp (ident, "special_member_function"))
	return eval_is_special_member_function (h);
      if (!strcmp (ident, "constructor"))
	return eval_is_constructor (h);
      if (!strcmp (ident, "default_constructor"))
	return eval_is_default_constructor (h);
      if (!strcmp (ident, "copy_constructor"))
	return eval_is_copy_constructor (h);
      if (!strcmp (ident, "move_constructor"))
	return eval_is_move_constructor (h);
      if (!strcmp (ident, "assignment"))
	return eval_is_assignment (h);
      if (!strcmp (ident, "copy_assignment"))
	return eval_is_copy_assignment (h);
      if (!strcmp (ident, "move_assignment"))
	return eval_is_move_assignment (h);
      if (!strcmp (ident, "destructor"))
	return eval_is_destructor (h);
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
      if (!strcmp (ident, "arithmetic_type"))
	return eval_is_arithmetic_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "object_type"))
	return eval_is_object_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "scalar_type"))
	return eval_is_scalar_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "member_pointer_type"))
	return eval_is_member_pointer_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "const_type"))
	return eval_is_const_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "volatile_type"))
	return eval_is_volatile_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "trivially_copyable_type"))
	return eval_is_trivially_copyable_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "trivially_relocatable_type"))
	return eval_is_trivially_relocatable_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "replaceable_type"))
	return eval_is_replaceable_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "standard_layout_type"))
	return eval_is_standard_layout_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "empty_type"))
	return eval_is_empty_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "polymorphic_type"))
	return eval_is_polymorphic_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "abstract_type"))
	return eval_is_abstract_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "final_type"))
	return eval_is_final_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "aggregate_type"))
	return eval_is_aggregate_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "consteval_only_type"))
	return eval_is_consteval_only_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "signed_type"))
	return eval_is_signed_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "unsigned_type"))
	return eval_is_unsigned_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "bounded_array_type"))
	return eval_is_bounded_array_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "unbounded_array_type"))
	return eval_is_unbounded_array_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "scoped_enum_type"))
	return eval_is_scoped_enum_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "default_constructible_type"))
	return eval_is_default_constructible_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "copy_constructible_type"))
	return eval_is_copy_constructible_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "move_constructible_type"))
	return eval_is_move_constructible_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "copy_assignable_type"))
	return eval_is_copy_assignable_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "move_assignable_type"))
	return eval_is_move_assignable_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "destructible_type"))
	return eval_is_destructible_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "trivially_default_constructible_type"))
	return eval_is_trivially_default_constructible_type (loc, ctx, h,
							     jump_target);
      if (!strcmp (ident, "trivially_copy_constructible_type"))
	return eval_is_trivially_copy_constructible_type (loc, ctx, h,
							  jump_target);
      if (!strcmp (ident, "trivially_move_constructible_type"))
	return eval_is_trivially_move_constructible_type (loc, ctx, h,
							  jump_target);
      if (!strcmp (ident, "trivially_copy_assignable_type"))
	return eval_is_trivially_copy_assignable_type (loc, ctx, h,
						       jump_target);
      if (!strcmp (ident, "trivially_move_assignable_type"))
	return eval_is_trivially_move_assignable_type (loc, ctx, h,
						       jump_target);
      if (!strcmp (ident, "trivially_destructible_type"))
	return eval_is_trivially_destructible_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "nothrow_default_constructible_type"))
	return eval_is_nothrow_default_constructible_type (loc, ctx, h,
							   jump_target);
      if (!strcmp (ident, "nothrow_copy_constructible_type"))
	return eval_is_nothrow_copy_constructible_type (loc, ctx, h,
							jump_target);
      if (!strcmp (ident, "nothrow_move_constructible_type"))
	return eval_is_nothrow_move_constructible_type (loc, ctx, h,
							jump_target);
      if (!strcmp (ident, "nothrow_copy_assignable_type"))
	return eval_is_nothrow_copy_assignable_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "nothrow_move_assignable_type"))
	return eval_is_nothrow_move_assignable_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "nothrow_destructible_type"))
	return eval_is_nothrow_destructible_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "nothrow_relocatable_type"))
	return eval_is_nothrow_relocatable_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "fundamental_type"))
	return eval_is_fundamental_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "compound_type"))
	return eval_is_compound_type (loc, ctx, h, jump_target);
      if (!strcmp (ident, "same_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_same_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "base_of_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_base_of_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "virtual_base_of_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_virtual_base_of_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "convertible_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_convertible_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "nothrow_convertible_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_nothrow_convertible_type (loc, ctx, h, h1,
						   jump_target);
	}
      if (!strcmp (ident, "layout_compatible_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_layout_compatible_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "pointer_interconvertible_base_of_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_pointer_interconvertible_base_of_type (loc, ctx, h,
								h1,
								jump_target);
	}
      if (!strcmp (ident, "assignable_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_assignable_type (loc, ctx, h, h1, jump_target);
	}
      if (!strcmp (ident, "trivially_assignable_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_trivially_assignable_type (loc, ctx, h, h1,
						    jump_target);
	}
      if (!strcmp (ident, "nothrow_assignable_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  return eval_is_nothrow_assignable_type (loc, ctx, h, h1,
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
      if (!strcmp (ident, "internal_linkage"))
	return eval_has_internal_linkage (h, kind);
      if (!strcmp (ident, "module_linkage"))
	return eval_has_module_linkage (h, kind);
      if (!strcmp (ident, "external_linkage"))
	return eval_has_external_linkage (h, kind);
      if (!strcmp (ident, "c_language_linkage"))
	return eval_has_c_language_linkage (h, kind);
      if (!strcmp (ident, "linkage"))
	return eval_has_linkage (h, kind);
      if (!strcmp (ident, "template_arguments"))
	return eval_has_template_arguments (h);
      if (!strcmp (ident, "parent"))
	return eval_has_parent (h, kind);
      if (!strcmp (ident, "ellipsis_parameter"))
	return eval_has_ellipsis_parameter (h);
      if (!strcmp (ident, "virtual_destructor"))
	return eval_has_virtual_destructor (loc, ctx, h, jump_target);
      if (!strcmp (ident, "unique_object_representations"))
	return eval_has_unique_object_representations (loc, ctx, h,
						       jump_target);
      goto not_found;
    }

  if (id_equal (name, "source_location_of"))
    return eval_source_location_of (loc, h, TREE_TYPE (call));
  if (id_equal (name, "dealias"))
    return eval_dealias (loc, ctx, h, jump_target);
  if (id_equal (name, "template_of"))
    return eval_template_of (loc, ctx, h, jump_target);
  if (id_equal (name, "template_arguments_of"))
    return eval_template_arguments_of (loc, ctx, h, jump_target);
  if (id_equal (name, "parameters_of"))
    return eval_parameters_of (loc, ctx, h, jump_target);
  if (id_equal (name, "enumerators_of"))
    return eval_enumerators_of (loc, ctx, h, jump_target);
  if (id_equal (name, "variable_of"))
    return eval_variable_of (loc, ctx, h, kind, jump_target);
  if (id_equal (name, "return_type_of"))
    return eval_return_type_of (loc, ctx, h, kind, jump_target);
  if (id_equal (name, "offset_of"))
    return eval_offset_of (loc, ctx, h, TREE_TYPE (call), jump_target);
  if (id_equal (name, "size_of"))
    return eval_size_of (loc, ctx, h, kind, TREE_TYPE (call), jump_target);
  if (id_equal (name, "bit_size_of"))
    return eval_bit_size_of (loc, ctx, h, kind, TREE_TYPE (call), jump_target);
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
  if (id_equal (name, "remove_reference"))
    return eval_remove_reference (loc, ctx, h, jump_target);
  if (id_equal (name, "add_lvalue_reference"))
    return eval_add_lvalue_reference (loc, ctx, h, jump_target);
  if (id_equal (name, "add_rvalue_reference"))
    return eval_add_rvalue_reference (loc, ctx, h, jump_target);
  if (id_equal (name, "make_signed"))
    return eval_make_signed (loc, ctx, h, false, jump_target);
  if (id_equal (name, "make_unsigned"))
    return eval_make_signed (loc, ctx, h, true, jump_target);
  if (id_equal (name, "remove_extent"))
    return eval_remove_extent (loc, ctx, h, jump_target);
  if (id_equal (name, "remove_all_extents"))
    return eval_remove_all_extents (loc, ctx, h, jump_target);
  if (id_equal (name, "remove_pointer"))
    return eval_remove_pointer (loc, ctx, h, jump_target);
  if (id_equal (name, "add_pointer"))
    return eval_add_pointer (loc, ctx, h, jump_target);
  if (id_equal (name, "annotations_of"))
    return eval_annotations_of (loc, ctx, h, kind, NULL_TREE, jump_target);
  if (id_equal (name, "annotations_of_with_type"))
    {
      tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			  jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      tree h1 = REFLECT_EXPR_HANDLE (i1);
      return eval_annotations_of (loc, ctx, h, kind, h1, jump_target);
    }
  if (id_equal (name, "type_of"))
    return eval_type_of (loc, ctx, h, kind, jump_target);
  if (!strcmp (ident, "operator_of"))
    return eval_operator_of (loc, ctx, h, jump_target, TREE_TYPE (call));
  if (id_equal (name, "parent_of"))
    return eval_parent_of (loc, ctx, h, kind, jump_target);
  if (id_equal (name, "reference_constructs_from_temporary"))
    {
      tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			  jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      tree h1 = REFLECT_EXPR_HANDLE (i1);
      return eval_reference_constructs_from_temporary (loc, ctx, h, h1,
						       jump_target);
    }
  if (id_equal (name, "reference_converts_from_temporary"))
    {
      tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			  jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      tree h1 = REFLECT_EXPR_HANDLE (i1);
      return eval_reference_converts_from_temporary (loc, ctx, h, h1,
						     jump_target);
    }
  if (id_equal (name, "rank"))
    return eval_rank (loc, ctx, h, jump_target);
  if (id_equal (name, "extent"))
    {
      tree i = get_nth_callarg (call, 1);
      location_t loc = cp_expr_loc_or_input_loc (i);
      i = cxx_eval_constant_expression (ctx, i, vc_prvalue,
					non_constant_p, overflow_p,
					jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      return eval_extent (loc, ctx, h, i, jump_target);
    }

not_found:
  sorry ("%qE", name);
  return error_mark_node;
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
compare_reflections (tree lhs, tree rhs)
{
  do
    {
      if (REFLECT_EXPR_KIND (lhs) != REFLECT_EXPR_KIND (rhs))
	return false;
      lhs = REFLECT_EXPR_HANDLE (lhs);
      rhs = REFLECT_EXPR_HANDLE (rhs);
    }
  while (REFLECT_EXPR_P (lhs) && REFLECT_EXPR_P (rhs));

  /* TEMPLATE_DECLs are wrapped in an OVERLOAD.  When we have

       template_of (^^fun_tmpl<int>) == ^^fun_tmpl

     the RHS will be OVERLOAD<TEMPLATE_DECL> but the LHS will
     only be TEMPLATE_DECL.  They should compare equal, though.  */
  // ??? Can we do something better?
  rhs = OVL_FIRST (MAYBE_BASELINK_FUNCTIONS (rhs));
  lhs = OVL_FIRST (MAYBE_BASELINK_FUNCTIONS (lhs));

  return lhs == rhs;
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
