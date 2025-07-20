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

  /* Is the call from std::meta?  */
  fndecl = decl_namespace_context (fndecl);
  return DECL_NAMESPACE_STD_META_P (fndecl);
}

/* Extract the reflection argument from a metafunction call CALL.  */

static tree
get_info (tree call)
{
  gcc_checking_assert (call_expr_nargs (call) > 0);
  tree info = CALL_EXPR_ARG (call, 0);
  gcc_checking_assert (REFLECTION_TYPE_P (TREE_TYPE (info)));
  info = cxx_constant_value (info);
  return info;
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
eval_has_identifier (tree t)
{
  if (TREE_CODE (t) == TYPE_DECL)
    t = TREE_TYPE (t);
  // TODO
  if (CLASS_TYPE_P (t) && TYPE_NAME (t))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Expand a call to a metafunction.  CALL is the CALL_EXPR.  */

tree
process_metafunction (tree call)
{
  tree info = get_info (call);
  /* Mapping name -> value would be a perfect use for a trie.  prime-paths.cc
     implements a trie.  */
  tree name = DECL_NAME (cp_get_callee_fndecl_nofold (call));

  if (id_equal (name, "has_identifier"))
    return eval_has_identifier (REFLECT_EXPR_HANDLE (info));
  else
    {
      sorry ("%qE", name);
      return NULL_TREE;
    }
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
  else if (current_function_decl
	   && LAMBDA_FUNCTION_P (current_function_decl)
	   && outer_automatic_var_p (t))
    {
      error_at (loc, "%<^^%> cannot be applied a local entity for which "
		"there is an intervening lambda expression");
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

  /* Otherwise, if the template-name names a function template F,
     then the template-name interpreted as an id-expression shall
     denote an overload set containing only F.  R represents F.

     When we have:
       template<typename T>
       void foo (T) {}
       constexpr auto a = ^^foo;
     we will get an OVERLOAD containing only one function.  */
  t = MAYBE_BASELINK_FUNCTIONS (t);
  if (OVL_P (t))
    {
      if (!OVL_SINGLE_P (t))
	{
	  error_at (loc, "cannot take the reflection of an overload set");
	  return error_mark_node;
	}
    }
  /* [expr.reflect] If the id-expression denotes an overload set S,
     overload resolution for the expression &S with no target shall
     select a unique function; R represents that function.

     We need to resolve TEMPLATE_ID_EXPRs so that they don't get into
     cp_genericize_r.  */
  else if (!processing_template_decl)
    t = resolve_nondeduced_context_or_error (t, tf_warning_or_error);

  /* For injected-class-name, use the main variant so that comparing
     reflections works (cf. compare3.C).  */
  if (RECORD_OR_UNION_TYPE_P (t) && DECL_SELF_REFERENCE_P (TYPE_NAME (t)))
    t = TYPE_MAIN_VARIANT (t);

  if (t == error_mark_node)
    return error_mark_node;

  return get_reflection_raw (loc, t);
}

/* Return a null reflection value.  */

tree
get_null_reflection ()
{
  return get_reflection_raw (UNKNOWN_LOCATION, unknown_type_node);
}

/* Splice reflection REFL; i.e., return its entity.  */

// XXX The errors may be emitted multiple times.  Add tentative_p?
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

/* Give an error if a consteval-only expression in EXPR is used outside
   a manifestly constant-evaluated context.  */

void
check_out_of_consteval_use (tree expr)
{
  if (in_immediate_context ())
    return;

  auto walker = [](tree *tp, int *walk_subtrees, void *) -> tree
    {
      tree t = *tp;

      /* No need to look into types or unevaluated operands.  */
      if (TYPE_P (t) || unevaluated_p (TREE_CODE (t))
	  /* This will be checked in cp_fold_immediate_r.  */
	  || TREE_CODE (t) == INIT_EXPR)
	{
	  *walk_subtrees = false;
	  return NULL_TREE;
	}

      if (REFLECT_EXPR_P (t)
	  || (VAR_P (t) && consteval_only_var_p (t)))
	error_at (cp_expr_loc_or_input_loc (t),
		  "consteval-only expressions are only allowed in "
		  "manifestly constant-evaluated context");

      return NULL_TREE;
    };

  cp_walk_tree_without_duplicates (&expr, walker, nullptr);
}

/* A walker for consteval_only_var_p.  It cannot be a lambda, because we
   have to call this recursively, sigh.  */

static tree
consteval_only_var_r (tree *tp, int *, void *data)
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
	if (tree r = cp_walk_tree (&TREE_TYPE (member), consteval_only_var_r,
				   visited, visited))
	  return r;

  return NULL_TREE;
}

/* True if VAR, a decl, is a consteval-only type as per
   [basic.types.general].  Currently, that means it has reflection type,
   or is compounded from it.  */

bool
consteval_only_var_p (tree var)
{
  if (!flag_reflection)
    return false;

  /* Classes with std::meta::info members are also consteval-only.  */
  hash_set<tree> visited;
  return !!cp_walk_tree (&TREE_TYPE (var), consteval_only_var_r, &visited,
			 &visited);
}

/* Return true if the reflections LHS and RHS are equal.  */

bool
compare_reflections (const_tree lhs, const_tree rhs)
{
  return REFLECT_EXPR_HANDLE (lhs) == REFLECT_EXPR_HANDLE (rhs);
}
