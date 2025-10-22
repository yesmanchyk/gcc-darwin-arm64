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
#include "c-family/c-pragma.h" // for parse_in
#include "gimplify.h" // for unshare_expr

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

/* If PARM_DECL comes from an earlier reflection of a function parameter
   and function definition is seen after that, DECL_ARGUMENTS is
   overwritten and so the old PARM_DECL is no longer present in the
   DECL_ARGUMENTS (DECL_CONTEXT (parm)) chain.  Return corresponding
   PARM_DECL which is in the chain.  */

static tree
maybe_update_function_parm (tree parm)
{
  if (!OLD_PARM_DECL_P (parm))
    return parm;
  tree fn = DECL_CONTEXT (parm);
  int oldlen = list_length (parm);
  int newlen = list_length (DECL_ARGUMENTS (fn));
  gcc_assert (newlen >= oldlen);
  tree ret = DECL_ARGUMENTS (fn);
  int n = newlen - oldlen;
  while (n)
    {
      ret = DECL_CHAIN (ret);
      --n;
    }
  return ret;
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

/* Helper function for get_range_elts, called through cp_walk_tree.  */

static tree
replace_parm_r (tree *tp, int *walk_subtrees, void *data)
{
  tree *p = (tree *) data;
  if (*tp == p[0])
    *tp = p[1];
  else if (TYPE_P (*tp))
    *walk_subtrees = 0;
  return NULL_TREE;
}

static tree throw_exception (location_t, const constexpr_ctx *, const char *,
			     tree, tree *);

/* Kinds for get_range_elts.  */

enum get_range_elts_kind {
  GET_INFO_VEC,
  REFLECT_CONSTANT_STRING,
  REFLECT_CONSTANT_ARRAY
};

/* Extract the N-th input_range argument from a metafunction call CALL
   and return it as TREE_VEC or STRING_CST or CONSTRUCTOR.  Helper function
   for get_info_vec, eval_reflect_constant_string and
   eval_reflect_constant_array.  For GET_INFO_VEC kind, <meta> ensures
   the argument is reference to reflection_range concept and so both
   range_value_t is info and range_refernce_t is cv info or cv info & or
   cv info &&.  */

static tree
get_range_elts (location_t loc, const constexpr_ctx *ctx, tree call, int n,
		bool *non_constant_p, bool *overflow_p, tree *jump_target,
		get_range_elts_kind kind)
{
  gcc_checking_assert (call_expr_nargs (call) > n);
  tree arg = get_nth_callarg (call, n);
  tree parm = DECL_ARGUMENTS (cp_get_callee_fndecl_nofold (call));
  for (int i = 0; i < n; ++i)
    parm = DECL_CHAIN (parm);
  tree type = TREE_TYPE (arg);
  gcc_checking_assert (TYPE_REF_P (type));
  arg = cxx_eval_constant_expression (ctx, arg, vc_prvalue, non_constant_p,
				      overflow_p, jump_target);
fail_ret:
  if (*jump_target)
    return NULL_TREE;
  if (*non_constant_p)
    return call;
  tree map[2] = { parm, arg };
  /* To speed things up, check
     if constexpr (std::ranges::contiguous_range <_R>).  */
  tree ranges_ns = lookup_qualified_name (std_node, "ranges");
  if (TREE_CODE (ranges_ns) != NAMESPACE_DECL)
    {
      error_at (loc, "%<std::ranges%> is not a namespace");
      *non_constant_p = true;
      return call;
    }
  tree contiguous_range
    = lookup_qualified_name (ranges_ns, "contiguous_range");
  if (TREE_CODE (contiguous_range) != TEMPLATE_DECL
      || !concept_definition_p (contiguous_range))
    contiguous_range = NULL_TREE;
  else
    {
      tree args = make_tree_vec (1);
      TREE_VEC_ELT (args, 0) = TREE_TYPE (type);
      contiguous_range = build2_loc (loc, TEMPLATE_ID_EXPR, boolean_type_node,
				     contiguous_range, args);
      if (!integer_nonzerop (maybe_constant_value (contiguous_range)))
	contiguous_range = NULL_TREE;
    }
  tree valuet = meta_info_type_node;
  tree ret = NULL_TREE;
  if (kind != GET_INFO_VEC)
    {
      tree args = make_tree_vec (1);
      TREE_VEC_ELT (args, 0) = TREE_TYPE (type);
      tree inst = lookup_template_class (get_identifier ("range_value_t"),
					 args, /*in_decl*/NULL_TREE,
					 /*context*/ranges_ns,
					 tf_warning_or_error);
      inst = complete_type (inst);
      if (inst == error_mark_node)
	{
	  *non_constant_p = true;
	  return call;
	}
      valuet = TYPE_MAIN_VARIANT (inst);
      if (kind == REFLECT_CONSTANT_STRING
	  && valuet != char_type_node
	  && valuet != wchar_type_node
	  && valuet != char8_type_node
	  && valuet != char16_type_node
	  && valuet != char32_type_node)
	{
	  if (!cxx_constexpr_quiet_p (ctx))
	    error_at (loc, "%<reflect_constant_string%> called with %qT "
			   "%<std::ranges::range_value_t%> rather than "
			   "%<char%>, %<wchar_t%>, %<char8_t%>, %<char16_t%> "
			   "or %<char32_t%>", valuet);
	  *non_constant_p = true;
	  return call;
	}
      /* Check for the reflect_object_string special-case, where r
	 refers to a string literal.  In that case CharT() should not
	 be appended.  */
      if (kind == REFLECT_CONSTANT_STRING
	  && TREE_CODE (TREE_TYPE (type)) == ARRAY_TYPE
	  && TYPE_MAIN_VARIANT (TREE_TYPE (TREE_TYPE (type))) == valuet
	  && TYPE_DOMAIN (TREE_TYPE (type)))
	{
	  tree a = arg;
	  tree maxv = TYPE_MAX_VALUE (TYPE_DOMAIN (TREE_TYPE (type)));
	  STRIP_NOPS (a);
	  tree at;
	  if (TREE_CODE (a) == ADDR_EXPR
	      && TREE_CODE (TREE_OPERAND (a, 0)) == STRING_CST
	      && tree_fits_uhwi_p (maxv)
	      && ((unsigned) TREE_STRING_LENGTH (TREE_OPERAND (a, 0))
		  == ((tree_to_uhwi (maxv) + 1)
		       * tree_to_uhwi (TYPE_SIZE_UNIT (valuet))))
	      && (at = TREE_TYPE (TREE_OPERAND (a, 0)))
	      && TREE_CODE (at) == ARRAY_TYPE
	      && TYPE_MAIN_VARIANT (TREE_TYPE (at)) == valuet
	      && TYPE_DOMAIN (at)
	      && tree_int_cst_equal (maxv, TYPE_MAX_VALUE (TYPE_DOMAIN (at))))
	    return TREE_OPERAND (a, 0);
	}
      if (kind == REFLECT_CONSTANT_ARRAY)
	{
	  if (!structural_type_p (valuet))
	    {
	      if (!cxx_constexpr_quiet_p (ctx))
		{
		  auto_diagnostic_group d;
		  error_at (loc, "%<reflect_constant_array%> argument with "
				 "%qT %<std::ranges::range_value_t%> which "
				 "is not a structural type", valuet);
		  structural_type_p (valuet, true);
		}
	      *non_constant_p = true;
	      return call;
	    }
	  tree cvaluet
	    = cp_build_qualified_type (valuet, cp_type_quals (valuet)
					       | TYPE_QUAL_CONST);
	  TREE_VEC_ELT (args, 0)
	    = cp_build_reference_type (cvaluet, /*rval=*/false);
	  if (!is_xible (INIT_EXPR, valuet, args))
	    {
	      if (!cxx_constexpr_quiet_p (ctx))
		error_at (loc, "%<reflect_constant_array%> argument with %qT "
			       "%<std::ranges::range_value_t%> which is not "
			       "copy constructible", valuet);
	      *non_constant_p = true;
	      return call;
	    }
	  TREE_VEC_ELT (args, 0) = TREE_TYPE (type);
	  inst = lookup_template_class (get_identifier ("range_reference_t"),
					args, /*in_decl*/NULL_TREE,
					/*context*/ranges_ns,
					tf_warning_or_error);
	  inst = complete_type (inst);
	  if (inst == error_mark_node)
	    {
	      *non_constant_p = true;
	      return call;
	    }
	  tree referencet = TYPE_MAIN_VARIANT (inst);
	  TREE_VEC_ELT (args, 0) = referencet;
	  if (!is_xible (INIT_EXPR, valuet, args))
	    {
	      if (!cxx_constexpr_quiet_p (ctx))
		error_at (loc, "%<reflect_constant_array%> argument with %qT "
			       "%<std::ranges::range_value_t%> which is not "
			       "constructible from %qT "
			       "%<std::ranges::range_reference_t%>",
			valuet, referencet);
	      *non_constant_p = true;
	      return call;
	    }
	}
    }
  auto_vec<tree, 32> retvec;
  tree p = convert_from_reference (parm);
  auto obj_call = [=, &map] (tree obj, tsubst_flags_t complain) {
    releasing_vec args;
    vec_safe_push (args, p);
    tree call = finish_call_expr (obj, &args, true, false, complain);
    if (call == error_mark_node)
      return call;
    cp_walk_tree (&call, replace_parm_r, map, NULL);
    if (complain != tf_none)
      return call;
    call = cxx_eval_constant_expression (ctx, call, vc_prvalue, non_constant_p,
					 overflow_p, jump_target);
    if (*jump_target || *non_constant_p)
      return NULL_TREE;
    return call;
  };
  auto ret_retvec = [=, &retvec] () {
    unsigned HOST_WIDE_INT sz = retvec.length ();
    for (size_t i = 0; i < sz; ++i)
      {
	if (INTEGRAL_TYPE_P (valuet))
	  {
	    if (TREE_CODE (retvec[i]) != INTEGER_CST)
	      return throw_exception (loc, ctx,
				      N_("array element not a constant integer"),
				      retvec[i], jump_target);
	  }
	else
	  {
	    gcc_assert (kind == REFLECT_CONSTANT_ARRAY);
	    tree expr = convert_reflect_constant_arg (valuet, retvec[i]);
	    if (expr == error_mark_node)
	      return throw_exception (loc, ctx, N_("reflect_constant failed"),
				      retvec[i], jump_target);
	    if (VAR_P (expr))
	      expr = unshare_expr (DECL_INITIAL (expr));
	    retvec[i] = expr;
	  }
      }
    if (kind == REFLECT_CONSTANT_ARRAY && sz == 0)
      {
	/* Return std::array <valuet, 0> {}.  */
	tree args = make_tree_vec (2);
	TREE_VEC_ELT (args, 0) = valuet;
	TREE_VEC_ELT (args, 1) = size_zero_node;
	tree inst = lookup_template_class (get_identifier ("array"), args,
					   /*in_decl*/NULL_TREE,
					   /*context*/std_node,
					   tf_warning_or_error);
	tree type = complete_type (inst);
	if (type == error_mark_node)
	  {
	    *non_constant_p = true;
	    return call;
	  }
	tree ctor = build_constructor (init_list_type_node, nullptr);
	CONSTRUCTOR_IS_DIRECT_INIT (ctor) = true;
	TREE_CONSTANT (ctor) = true;
	TREE_STATIC (ctor) = true;
	tree r = finish_compound_literal (type, ctor, tf_warning_or_error,
					  fcl_functional);
	if (TREE_CODE (r) == TARGET_EXPR)
	  r = TARGET_EXPR_INITIAL (r);
	return r;
      }
    unsigned esz = tree_to_uhwi (TYPE_SIZE_UNIT (valuet));
    unsigned last = kind == REFLECT_CONSTANT_STRING ? esz : 0;
    tree index = build_index_type (size_int (last ? sz : sz - 1));
    tree at = build_array_type (valuet, index);
    at = cp_build_qualified_type (at, TYPE_QUAL_CONST);
    if (kind == REFLECT_CONSTANT_STRING
        || ((valuet == char_type_node
	     || valuet == wchar_type_node
	     || valuet == char8_type_node
	     || valuet == char16_type_node
	     || valuet == char32_type_node)
	    && integer_zerop (retvec.last ())))
      {
	unsigned HOST_WIDE_INT szt = sz * esz;
	char *p;
	if (szt < 4096)
	  p = XALLOCAVEC (char, szt + last);
	else
	  p = XNEWVEC (char, szt + last);
	for (size_t i = 0; i < sz; ++i)
	  native_encode_expr (retvec[i], (unsigned char *) p + i * esz,
			      esz, 0);
	if (last)
	  memset (p + szt, '\0', last);
	tree ret = build_string (szt + last, p);
	TREE_TYPE (ret) = at;
	TREE_CONSTANT (ret) = 1;
	TREE_READONLY (ret) = 1;
	TREE_STATIC (ret) = 1;
	if (szt >= 4096)
	  XDELETEVEC (p);
	return ret;
      }
    vec<constructor_elt, va_gc> *elts = nullptr;
    for (unsigned i = 0; i < sz; ++i)
      CONSTRUCTOR_APPEND_ELT (elts, bitsize_int (i), retvec[i]);
    return build_constructor (at, elts);
  };
  /* If true, call std::ranges::data (p) and std::ranges::size (p)
     and if that works out and what the former returns can be handled,
     grab the elements from the initializer of the decl pointed by the
     first expression.  p has to be convert_from_reference (PARM_DECL)
     rather than its value, otherwise it is not considered lvalue.  */
  if (contiguous_range)
    {
      tree data = lookup_qualified_name (ranges_ns, "data");
      tree size = lookup_qualified_name (ranges_ns, "size");
      if (TREE_CODE (data) != VAR_DECL || TREE_CODE (size) != VAR_DECL)
	goto non_contiguous;
      data = obj_call (data, tf_none);
      if (error_operand_p (data))
	goto non_contiguous;
      if (data == NULL_TREE)
	goto fail_ret;
      size = obj_call (size, tf_none);
      if (error_operand_p (size))
	goto non_contiguous;
      if (size == NULL_TREE)
	goto fail_ret;
      if (!tree_fits_uhwi_p (size) || tree_to_uhwi (size) > INT_MAX)
	goto non_contiguous;
      if (integer_zerop (size))
	{
	  if (kind == GET_INFO_VEC)
	    return make_tree_vec (0);
	  return ret_retvec ();
	}
      STRIP_NOPS (data);
      unsigned HOST_WIDE_INT minidx = 0, pplus = 0;
      if (TREE_CODE (data) == POINTER_PLUS_EXPR
	  && tree_fits_uhwi_p (TREE_OPERAND (data, 1))
	  && !wi::neg_p (wi::to_wide (TREE_OPERAND (data, 1))))
	{
	  pplus = tree_to_uhwi (TREE_OPERAND (data, 1));
	  data = TREE_OPERAND (data, 0);
	  STRIP_NOPS (data);
	}
      if (TREE_CODE (data) != ADDR_EXPR)
	goto non_contiguous;
      data = TREE_OPERAND (data, 0);
      if (TREE_CODE (data) == ARRAY_REF
	  && tree_fits_uhwi_p (TREE_OPERAND (data, 1)))
	{
	  minidx = tree_to_uhwi (TREE_OPERAND (data, 1));
	  data = TREE_OPERAND (data, 0);
	}
      data = cxx_eval_constant_expression (ctx, data, vc_prvalue,
					   non_constant_p, overflow_p,
					   jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      if (TREE_CODE (TREE_TYPE (data)) != ARRAY_TYPE
	  || TYPE_MAIN_VARIANT (TREE_TYPE (TREE_TYPE (data))) != valuet)
	goto non_contiguous;
      if (pplus
	  && (pplus % tree_to_uhwi (TYPE_SIZE_UNIT (valuet))) != 0)
	goto non_contiguous;
      minidx += pplus / tree_to_uhwi (TYPE_SIZE_UNIT (valuet));
      if (kind != GET_INFO_VEC && TREE_CODE (data) == STRING_CST)
	{
	  unsigned esz = tree_to_uhwi (TYPE_SIZE_UNIT (valuet));
	  unsigned HOST_WIDE_INT sz = tree_to_uhwi (size) * esz;
	  if (minidx > INT_MAX
	      || (unsigned) TREE_STRING_LENGTH (data) < sz + minidx * esz)
	    goto non_contiguous;
	  if (kind == REFLECT_CONSTANT_ARRAY && sz == 0)
	    return ret_retvec ();
	  tree index
	    = build_index_type (size_int ((kind == REFLECT_CONSTANT_ARRAY
					   ? -1 : 0) + tree_to_uhwi (size)));
	  tree at = build_array_type (valuet, index);
	  at = cp_build_qualified_type (at, TYPE_QUAL_CONST);
	  const unsigned char *q
	    = (const unsigned char *) TREE_STRING_POINTER (data);
	  q += minidx * esz;
	  if (kind == REFLECT_CONSTANT_ARRAY)
	    {
	      unsigned HOST_WIDE_INT i;
	      for (i = 0; i < esz; ++i)
		if (q[sz - esz + i])
		  break;
	      if (i != esz)
		{
		  /* Not a NUL terminated string.  Build a CONSTRUCTOR
		     instead.  */
		  for (i = 0; i < sz; i += esz)
		    {
		      tree t = native_interpret_expr (valuet, q + i, sz);
		      retvec.safe_push (t);
		    }
		  return ret_retvec ();
		}
	    }
	  char *p;
	  if (sz < 4096)
	    p = XALLOCAVEC (char, sz + esz);
	  else
	    p = XNEWVEC (char, sz + esz);
	  memcpy (p, q, sz);
	  memset (p + sz, '\0', esz);
	  ret = build_string (sz + (kind == REFLECT_CONSTANT_ARRAY
				    ? 0 : esz), p);
	  TREE_TYPE (ret) = at;
	  TREE_CONSTANT (ret) = 1;
	  TREE_READONLY (ret) = 1;
	  TREE_STATIC (ret) = 1;
	  if (sz >= 4096)
	    XDELETEVEC (p);
	  return ret;
	}
      if (TREE_CODE (data) != CONSTRUCTOR)
	goto non_contiguous;
      unsigned sz = tree_to_uhwi (size), i;
      unsigned HOST_WIDE_INT j = 0;
      tree *r, null = NULL_TREE;
      if (kind == GET_INFO_VEC)
	{
	  ret = make_tree_vec (sz);
	  r = TREE_VEC_BEGIN (ret);
	  null = get_null_reflection ();
	}
      else
	{
	  retvec.safe_grow (sz, true);
	  r = retvec.address ();
	}
      for (i = 0; i < sz; ++i)
	r[i] = null;
      tree field, value;
      FOR_EACH_CONSTRUCTOR_ELT (CONSTRUCTOR_ELTS (data), i, field, value)
	if (field == NULL_TREE)
	  {
	    if (j >= minidx && j - minidx < sz)
	      r[j - minidx] = value;
	    ++j;
	  }
	else if (TREE_CODE (field) == RANGE_EXPR)
	  {
	    tree lo = TREE_OPERAND (field, 0);
	    tree hi = TREE_OPERAND (field, 1);
	    if (!tree_fits_uhwi_p (lo) || !tree_fits_uhwi_p (hi))
	      goto non_contiguous;
	    unsigned HOST_WIDE_INT m = tree_to_uhwi (hi);
	    for (j = tree_to_uhwi (lo); j <= m; ++j)
	      if (j >= minidx && j - minidx < sz)
		r[j - minidx] = value;
	  }
	else if (tree_fits_uhwi_p (field))
	  {
	    j = tree_to_uhwi (field);
	    if (j >= minidx && j - minidx < sz)
	      r[j - minidx] = value;
	    ++j;
	  }
	else
	  goto non_contiguous;
      if (kind == GET_INFO_VEC)
	return ret;
      for (i = 0; i < sz; ++i)
	if (r[i] == NULL_TREE || !tree_fits_shwi_p (r[i]))
	  goto non_contiguous;
      return ret_retvec ();
    }
 non_contiguous:
  /* Otherwise, do it the slower way.  Initialize two temporaries,
     one to std::ranges::base (p) and another to std::ranges::end (p)
     and use a loop.  */
  tree begin = lookup_qualified_name (ranges_ns, "begin");
  tree end = lookup_qualified_name (ranges_ns, "end");
  if (TREE_CODE (begin) != VAR_DECL || TREE_CODE (end) != VAR_DECL)
    {
      error_at (loc, "missing %<std::ranges::begin%> or %<std::ranges::end%>");
      *non_constant_p = true;
      return call;
    }
  begin = obj_call (begin, tf_warning_or_error);
  if (error_operand_p (begin))
    {
      *non_constant_p = true;
      return call;
    }
  end = obj_call (end, tf_warning_or_error);
  if (error_operand_p (end))
    {
      *non_constant_p = true;
      return call;
    }
  if (!CLASS_TYPE_P (TREE_TYPE (begin)) && !POINTER_TYPE_P (TREE_TYPE (begin)))
    {
      error_at (loc, "incorrect type %qT of %<std::ranges::begin(arg)%>",
		TREE_TYPE (begin));
      *non_constant_p = true;
      return call;
    }
  if (VOID_TYPE_P (TREE_TYPE (end)))
    {
      error_at (loc, "incorrect type %qT of %<std::ranges::end(arg)%>",
		TREE_TYPE (end));
      *non_constant_p = true;
      return call;
    }
  begin = get_target_expr (begin);
  end = get_target_expr (end);
  begin = cxx_eval_constant_expression (ctx, begin, vc_glvalue, non_constant_p,
					overflow_p, jump_target);
  if (*jump_target || *non_constant_p)
    goto fail_ret;
  end = cxx_eval_constant_expression (ctx, end, vc_glvalue, non_constant_p,
				      overflow_p, jump_target);
  if (*jump_target || *non_constant_p)
    goto fail_ret;
  tree cmp = build_new_op (loc, NE_EXPR, LOOKUP_NORMAL, begin, end,
			   tf_warning_or_error);
  tree deref = build_new_op (loc, INDIRECT_REF, LOOKUP_NORMAL, begin,
			     NULL_TREE, tf_warning_or_error);
  tree inc = build_new_op (loc, PREINCREMENT_EXPR, LOOKUP_NORMAL, begin,
			   NULL_TREE, tf_warning_or_error);
  cmp = condition_conversion (cmp);
  if (error_operand_p (cmp)
      || error_operand_p (deref)
      || error_operand_p (inc))
    {
      *non_constant_p = true;
      return call;
    }
  // TODO: For REFLECT_CONSTANT_* handle proxy iterators.
  if (TYPE_MAIN_VARIANT (TREE_TYPE (deref)) != valuet)
    {
      if (!cxx_constexpr_quiet_p (ctx))
	error_at (loc, "unexpected type %qT of iterator dereference",
		  TREE_TYPE (deref));
      *non_constant_p = true;
      return call;
    }
  retvec.truncate (0);
  /* while (begin != end) { push (*begin); ++begin; }  */
  do
    {
      tree t = cxx_eval_constant_expression (ctx, cmp, vc_prvalue,
					     non_constant_p, overflow_p,
					     jump_target);
      if (*jump_target || *non_constant_p)
	goto fail_ret;
      if (integer_zerop (t))
	break;
      t = cxx_eval_constant_expression (ctx, deref, vc_prvalue, non_constant_p,
					overflow_p, jump_target);
      if (*jump_target || *non_constant_p)
	goto fail_ret;
      retvec.safe_push (t);
      cxx_eval_constant_expression (ctx, inc, vc_discard, non_constant_p,
				    overflow_p, jump_target);
      if (*jump_target || *non_constant_p)
	goto fail_ret;
    }
  while (true);
  if (kind != GET_INFO_VEC)
    return ret_retvec ();
  ret = make_tree_vec (retvec.length ());
  tree v;
  unsigned int i;
  FOR_EACH_VEC_ELT (retvec, i, v)
    TREE_VEC_ELT (ret, i) = v;
  return ret;
}

/* Extract the N-th reflection_range argument from a metafunction call CALL
   and return it as TREE_VEC.  */

static tree
get_info_vec (location_t loc, const constexpr_ctx *ctx, tree call, int n,
	      bool *non_constant_p, bool *overflow_p, tree *jump_target)
{
  return get_range_elts (loc, ctx, call, n, non_constant_p, overflow_p,
			 jump_target, GET_INFO_VEC);
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
	  && kind == REFLECT_UNDEF
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

/* Process std::meta::is_value.
   Returns: true if r represents a value.  Otherwise, false.  */

static tree
eval_is_value (reflect_kind kind)
{
  if (kind == REFLECT_VALUE)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Like get_info_vec, but throw exception if any of the elements aren't
   eval_is_type reflections and change their content to the corresponding
   REFLECT_EXPR_HANDLE.  */

static tree
get_type_info_vec (location_t loc, const constexpr_ctx *ctx, tree call, int n,
		   bool *non_constant_p, bool *overflow_p, tree *jump_target)
{
  tree vec = get_info_vec (loc, ctx, call, n, non_constant_p, overflow_p,
			   jump_target);
  if (*jump_target)
    return NULL_TREE;
  if (*non_constant_p)
    return call;
  for (int i = 0; i < TREE_VEC_LENGTH (vec); i++)
    {
      tree type = REFLECT_EXPR_HANDLE (TREE_VEC_ELT (vec, i));
      if (eval_is_type (type) != boolean_true_node)
	return throw_exception_nontype (loc, ctx, type, jump_target);
      TREE_VEC_ELT (vec, i) = type;
    }
  return vec;
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

/* Process std::meta::is_class_member.
   Returns: true if r represents a class member.  Otherwise, false.  */

static tree
eval_is_class_member (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);
  if (TREE_CODE (r) == CONST_DECL)
    {
      /* [class.mem.general]/5 - The enumerators of an unscoped enumeration
	 defined in the class are members of the class.  */
      if (UNSCOPED_ENUM_P (DECL_CONTEXT (r)))
	r = DECL_CONTEXT (r);
      else
	return boolean_false_node;
    }
  else if (TYPE_P (r) && typedef_variant_p (r))
    r = TYPE_NAME (r);
  else if (VAR_P (r) && DECL_ANON_UNION_VAR_P (r))
    return boolean_true_node;
  if (DECL_P (r) && DECL_CLASS_SCOPE_P (r))
    return boolean_true_node;
  else if (TYPE_P (r) && TYPE_CLASS_SCOPE_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_namespace_member.
   Returns: true if r represents a namespace member.  Otherwise, false.  */

static tree
eval_is_namespace_member (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);
  if (TREE_CODE (r) == CONST_DECL)
    {
      if (UNSCOPED_ENUM_P (DECL_CONTEXT (r)))
	r = DECL_CONTEXT (r);
      else
	return boolean_false_node;
    }
  else if (TYPE_P (r) && typedef_variant_p (r))
    r = TYPE_NAME (r);
  else if (VAR_P (r) && DECL_ANON_UNION_VAR_P (r))
    return boolean_false_node;
  if (r == global_namespace || r == unknown_type_node)
    return boolean_false_node;
  if (DECL_P (r) && DECL_NAMESPACE_SCOPE_P (r))
    return boolean_true_node;
  else if (TYPE_P (r) && TYPE_NAMESPACE_SCOPE_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_nonstatic_data_member.
   Returns: true if r represents a non-static data member.
   Otherwise, false.  */

static tree
eval_is_nonstatic_data_member (const_tree r)
{
  if (VAR_P (r) && DECL_ANON_UNION_VAR_P (r))
    return boolean_true_node;
  if (TREE_CODE (r) == FIELD_DECL && !DECL_UNNAMED_BIT_FIELD (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_static_member.
   Returns: true if r represents a static member.
   Otherwise, false.  */

static tree
eval_is_static_member (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);
  r = STRIP_TEMPLATE (r);
  if (TREE_CODE (r) == FUNCTION_DECL && DECL_STATIC_FUNCTION_P (r))
    return boolean_true_node;
  else if (VAR_P (r) && DECL_CLASS_SCOPE_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_default_member_initializer.
   Returns: true if r represents a non-static data member that has a default
   member initializer.  Otherwise, false.  */

static tree
eval_has_default_member_initializer (const_tree r)
{
  if (TREE_CODE (r) == FIELD_DECL
      && !DECL_UNNAMED_BIT_FIELD (r)
      && DECL_INITIAL (r) != NULL_TREE)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_static_storage_duration.
   Returns: true if r represents an object or variable that has static
   storage duration.  Otherwise, false.  */

static tree
eval_has_static_storage_duration (const_tree r, reflect_kind kind)
{
  if (eval_is_variable (r, kind) == boolean_true_node
      && decl_storage_duration (CONST_CAST_TREE (r)) == dk_static)
    return boolean_true_node;
  /* This includes DECL_NTTP_OBJECT_P objects.  */
  else if (eval_is_object (kind) == boolean_true_node)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_thread_storage_duration.
   Returns: true if r represents an object or variable that has thread
   storage duration.  Otherwise, false.  */

static tree
eval_has_thread_storage_duration (const_tree r, reflect_kind kind)
{
  if (eval_is_variable (r, kind) == boolean_true_node
      && decl_storage_duration (CONST_CAST_TREE (r)) == dk_thread)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::has_automatic_storage_duration.
   Returns: true if r represents an object or variable that has automatic
   storage duration.  Otherwise, false.  */

static tree
eval_has_automatic_storage_duration (const_tree r, reflect_kind kind)
{
  if (eval_is_variable (r, kind) == boolean_true_node
      && decl_storage_duration (CONST_CAST_TREE (r)) == dk_auto)
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_mutable_member.
   Returns: true if r represents a mutable non-static data member.
   Otherwise, false.  */

static tree
eval_is_mutable_member (tree r)
{
  if (VAR_P (r) && DECL_ANON_UNION_VAR_P (r))
    {
      tree v = DECL_VALUE_EXPR (r);
      if (v != error_mark_node && TREE_CODE (v) == COMPONENT_REF)
	r = TREE_OPERAND (v, 1);
    }
  if (TREE_CODE (r) == FIELD_DECL
      && !DECL_UNNAMED_BIT_FIELD (r)
      && DECL_MUTABLE_P (r))
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

/* Process std::meta::is_data_member_spec.
   Returns: true if r represents a data member description.
   Otherwise, false.  */

static tree
eval_is_data_member_spec (const_tree r, reflect_kind kind)
{
  if (kind == REFLECT_DATA_MEMBER_SPEC)
    {
      gcc_checking_assert (TREE_CODE (r) == TREE_VEC);
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

/* Process std::meta::has_default_argument.
   Returns: If r represents a parameter P of a function F, then:
   -- If F is a specialization of a templated function T, then true if there
      exists a declaration D of T that precedes some point in the evaluation
      context and D specifies a default argument for the parameter of T
      corresponding to P.  Otherwise, false.
   -- Otherwise, if there exists a declaration D of F that precedes some
      point in the evaluation context and D specifies a default argument
      for P, then true.
   Otherwise, false.  */

static tree
eval_has_default_argument (tree r, reflect_kind kind)
{
  if (eval_is_function_parameter (r, kind) == boolean_false_node)
    return boolean_false_node;
  r = maybe_update_function_parm (r);
  tree fn = DECL_CONTEXT (r);
  tree args = FUNCTION_FIRST_USER_PARM (fn);
  tree types = FUNCTION_FIRST_USER_PARMTYPE (fn);
  while (r != args)
    {
      args = DECL_CHAIN (args);
      types = TREE_CHAIN (types);
    }
  if (TREE_PURPOSE (types))
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
      && (stdarg_p (r) || TYPE_ARG_TYPES (r) == NULL_TREE))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_deleted.
   Returns: true if r represents a function that is deleted.
   Otherwise, false.  */

static tree
eval_is_deleted (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == BIT_NOT_EXPR
      && CLASS_TYPE_P (TREE_OPERAND (r, 0))
      && COMPLETE_TYPE_P (TREE_OPERAND (r, 0)))
    {
      tree t = TREE_OPERAND (r, 0);
      if (CLASSTYPE_LAZY_DESTRUCTOR (t))
	lazily_declare_fn (sfk_destructor, t);
      if (tree dtor = CLASSTYPE_DESTRUCTOR (t))
	r = dtor;
    }
  if (TREE_CODE (r) == FUNCTION_DECL && DECL_DELETED_FN (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_defaulted.
   Returns: true if r represents a function that is defaulted.
   Otherwise, false.  */

static tree
eval_is_defaulted (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == BIT_NOT_EXPR
      && CLASS_TYPE_P (TREE_OPERAND (r, 0))
      && COMPLETE_TYPE_P (TREE_OPERAND (r, 0)))
    {
      tree t = TREE_OPERAND (r, 0);
      if (CLASSTYPE_LAZY_DESTRUCTOR (t))
	lazily_declare_fn (sfk_destructor, t);
      if (tree dtor = CLASSTYPE_DESTRUCTOR (t))
	r = dtor;
    }
  if (TREE_CODE (r) == FUNCTION_DECL && DECL_DEFAULTED_FN (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_user_provided.
   Returns: true if r represents a function that is user-provided.
   Otherwise, false.  */

static tree
eval_is_user_provided (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == BIT_NOT_EXPR
      && CLASS_TYPE_P (TREE_OPERAND (r, 0))
      && COMPLETE_TYPE_P (TREE_OPERAND (r, 0)))
    {
      tree t = TREE_OPERAND (r, 0);
      if (CLASSTYPE_LAZY_DESTRUCTOR (t))
	lazily_declare_fn (sfk_destructor, t);
      if (tree dtor = CLASSTYPE_DESTRUCTOR (t))
	r = dtor;
    }
  if (TREE_CODE (r) == FUNCTION_DECL
      && user_provided_p (r)
      // TODO: user_provided_p is false for non-members defaulted on
      // first declaration.
      && (!DECL_NAMESPACE_SCOPE_P (r) || !DECL_DELETED_FN (r)))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_user_declared.
   Returns: true if r represents a function that is user-declared.
   Otherwise, false.  */

static tree
eval_is_user_declared (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  if (TREE_CODE (r) == BIT_NOT_EXPR
      && CLASS_TYPE_P (TREE_OPERAND (r, 0))
      && COMPLETE_TYPE_P (TREE_OPERAND (r, 0)))
    {
      tree t = TREE_OPERAND (r, 0);
      if (CLASSTYPE_LAZY_DESTRUCTOR (t))
	lazily_declare_fn (sfk_destructor, t);
      if (tree dtor = CLASSTYPE_DESTRUCTOR (t))
	r = dtor;
    }
  if (TREE_CODE (r) == FUNCTION_DECL && !DECL_ARTIFICIAL (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_explicit.
   Returns: true if r represents
   a member function that is declared explicit.
   Otherwise, false.
   If r represents a member function template
   that is declared explicit, is_explicit(r)
   is still false because in general such queries
   for templates cannot be answered.  */

static tree
eval_is_explicit (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);

  if (TREE_CODE (r) == FUNCTION_DECL && DECL_NONCONVERTING_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_bit_field.
   Returns: true if r represents a bit-field, or if r represents a data member
   description (T,N,A,W,NUA) for which W is not _|_.  Otherwise, false.  */

static tree
eval_is_bit_field (const_tree r, reflect_kind kind)
{
  if (TREE_CODE (r) == FIELD_DECL && DECL_C_BIT_FIELD (r))
    return boolean_true_node;
  else if (kind == REFLECT_DATA_MEMBER_SPEC && TREE_VEC_ELT (r, 3))
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
eval_is_conversion_function_template (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);

  if (DECL_FUNCTION_TEMPLATE_P (r) && DECL_CONV_FN_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_operator_function_template.
   Returns: true if r represents an operator function template.
   Otherwise, false.  */

static tree
eval_is_operator_function_template (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);

  if (DECL_FUNCTION_TEMPLATE_P (r))
    {
      r = STRIP_TEMPLATE (r);
      if (DECL_OVERLOADED_OPERATOR_P (r) && !DECL_CONV_FN_P (r))
	return boolean_true_node;
    }

  return boolean_false_node;
}

/* Process std::meta::is_literal_operator_template.
   Returns: true if r represents a literal operator template.
   Otherwise, false.  */

static tree
eval_is_literal_operator_template (tree r)
{
  /* No MAYBE_BASELINK_FUNCTIONS here because a literal operator
     template must be a non-member function template.  */
  r = OVL_FIRST (r);

  if (DECL_FUNCTION_TEMPLATE_P (r) && UDLIT_OPER_P (DECL_NAME (r)))
    return boolean_true_node;
  else
    return boolean_false_node;
}

/* Process std::meta::is_constructor_template.
   Returns: true if r represents a function that is an operator function
   template.  Otherwise, false.  */

static tree
eval_is_constructor_template (tree r)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);

  if (DECL_FUNCTION_TEMPLATE_P (r) && DECL_CONSTRUCTOR_P (r))
    return boolean_true_node;
  else
    return boolean_false_node;
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

/* Helper to build a string literal containing '\0' terminated NAME.
   ELT_TYPE must be either char_type_node or char8_type_node, and the
   function takes care of converting the name from SOURCE_CHARSET
   to ordinary literal charset resp. UTF-8 and returning the string
   literal.  Returns NULL_TREE if the conversion failed.  */

static tree
temp_string_literal (const char *name, tree elt_type)
{
  cpp_string cstr = { 0, 0 }, strname;
  size_t len = strlen (name) + 3; /* Two for '"'s.  One for NULL.  */
  char *namep = XNEWVEC (char, len);
  snprintf (namep, len, "\"%s\"", name);
  strname.text = (unsigned char *) namep;
  strname.len = len - 1;
  if (!cpp_interpret_string (parse_in, &strname, 1, &cstr,
			     elt_type == char_type_node
			     ? CPP_STRING : CPP_UTF8STRING))
    {
      XDELETEVEC (namep);
      return NULL_TREE;
    }
  name = (const char *) cstr.text;
  tree ret = build_string_literal (strlen (name) + 1, name, elt_type);
  free (const_cast <char *> (name));
  return ret;
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
	  tree str = temp_string_literal (name, elt_type);
	  /* Basic character set ought to be better convertible
	     into ordinary literal character set and must be always
	     convertible into UTF-8.  */
	  gcc_checking_assert (str);
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
      || eval_is_function_parameter (r, kind) == boolean_true_node
      || eval_is_object (kind) == boolean_true_node
      || kind == REFLECT_DATA_MEMBER_SPEC)
    return true;
  // TODO: direct base class relationship.
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
      r = maybe_update_function_parm (r);
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
  else if (kind == REFLECT_DATA_MEMBER_SPEC)
    r = TREE_VEC_ELT (r, 0);
  else if (eval_is_annotation (r) == boolean_true_node)
    {
      r = TREE_TYPE (TREE_VALUE (TREE_VALUE (r)));
      if (CLASS_TYPE_P (r))
	{
	  int quals = cp_type_quals (r);
	  quals |= TYPE_QUAL_CONST;
	  r = cp_build_qualified_type (r, quals);
	}
    }
  else if (TREE_CODE (r) == FIELD_DECL && DECL_BIT_FIELD_TYPE (r))
    r = DECL_BIT_FIELD_TYPE (r);
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

/* Process std::meta::is_noexcept.
   Returns: true if r represents a noexcept function type or a function
   with a non-throwing exception specification ([except.spec]).
   Otherwise, false.
   Note: If r represents a function template that is declared noexcept,
   is_noexcept (r) is still false because in general such queries
   for templates cannot be answered.  */

static tree
eval_is_noexcept (location_t loc, const constexpr_ctx *ctx, tree r,
		  tree *jump_target)
{
  if (eval_is_function (r) == boolean_true_node)
    {
      if (TREE_CODE (r) == BIT_NOT_EXPR)
	{
	  tree t = TREE_OPERAND (r, 0);
	  if (CLASSTYPE_LAZY_DESTRUCTOR (t))
	    lazily_declare_fn (sfk_destructor, t);
	  r = CLASSTYPE_DESTRUCTOR (t);
	  gcc_assert (r != NULL_TREE);
	  bool no_err = maybe_instantiate_noexcept (r);
	  gcc_assert (no_err);
	}

      if (TYPE_NOTHROW_P (TREE_TYPE (r)))
	return boolean_true_node;
      else
	return boolean_false_node;
    }

  if (eval_is_type (r) == boolean_true_node
      && eval_is_function_type (loc, ctx, r, jump_target) == boolean_true_node)
    {
      if (TYPE_NOTHROW_P (r))
	return boolean_true_node;
      else
	return boolean_false_node;
    }

  return boolean_false_node;
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
  if (kind == REFLECT_OBJECT
      || CONSTANT_CLASS_P (r)
      || r == global_namespace
      || kind == REFLECT_DATA_MEMBER_SPEC)
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
  // TODO: Handle direct base class relationship.
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
  r = maybe_update_function_parm (r);
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
      && (kind != REFLECT_DATA_MEMBER_SPEC || TREE_VEC_ELT (r, 3))
      /* TODO: direct base class relationship.  */)
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
      && kind != REFLECT_DATA_MEMBER_SPEC
      /* TODO: direct base class relationship.  */)
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
  else if (kind == REFLECT_DATA_MEMBER_SPEC && TREE_VEC_ELT (r, 3))
    return fold_convert (ret_type, TREE_VEC_ELT (r, 3));
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

/* Process std::meta::has_identifier.
   Returns:
   -- If r represents an entity that has a typedef name for linkage purposes,
      then true.
   -- Otherwise, if r represents an unnamed entity, then false.
   -- Otherwise, if r represents a class type, then !has_template_arguments(r).
   -- Otherwise, if r represents a function, then true if
      has_template_arguments(r) is false and the function is not a constructor,
      destructor, operator function, or conversion function.  Otherwise, false.
   -- Otherwise, if r represents a template, then true if r does not represent
      a constructor template, operator function template, or conversion
      function template.  Otherwise, false.
   -- Otherwise, if r represents the ith parameter of a function F that is an
      (implicit or explicit) specialization of a templated function T and the
      ith parameter of the instantiated declaration of T whose template
      arguments are those of F would be instantiated from a pack, then false.
   -- Otherwise, if r represents the parameter P of a function F, then let S
      be the set of declarations, ignoring any explicit instantiations, that
      precede some point in the evaluation context and that declare either F
      or a templated function of which F is a specialization; true if
      -- there is a declaration D in S that introduces a name N for either P
	 or the parameter corresponding to P in the templated function that
	 D declares and
      -- no declaration in S does so using any name other than N.
      Otherwise, false.
   -- Otherwise, if r represents a variable, then false if the declaration of
      that variable was instantiated from a function parameter pack.
      Otherwise, !has_template_arguments(r).
   -- Otherwise, if r represents a structured binding, then false if the
      declaration of that structured binding was instantiated from a
      structured binding pack.  Otherwise, true.
   -- Otherwise, if r represents a type alias, then !has_template_arguments(r).
   -- Otherwise, if r represents an enumerator, non-static-data member,
      namespace, or namespace alias, then true.
   -- Otherwise, if r represents a direct base class relationship, then
      has_identifier(type_of(r)).
   -- Otherwise, r represents a data member description (T,N,A,W,NUA); true if
      N is not _|_.  Otherwise, false.  */

static tree
eval_has_identifier (tree r, reflect_kind kind)
{
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);
  if (DECL_P (r)
      && kind != REFLECT_PARM
      && (!DECL_NAME (r) || IDENTIFIER_ANON_P (DECL_NAME (r))))
    return boolean_false_node;
  if (TYPE_P (r) && (!TYPE_NAME (r)
		     || (TYPE_ANON_P (r) && !typedef_variant_p (r))
		     || (DECL_P (TYPE_NAME (r))
			 && !DECL_NAME (TYPE_NAME (r)))))
    return boolean_false_node;
  if (CLASS_TYPE_P (r))
    {
      if (eval_has_template_arguments (r) == boolean_true_node)
	return boolean_false_node;
      else
	return boolean_true_node;
    }
  if (eval_is_function (r) == boolean_true_node)
    {
      if (eval_has_template_arguments (r) == boolean_true_node
	  || eval_is_constructor (r) == boolean_true_node
	  || eval_is_destructor (r) == boolean_true_node
	  || eval_is_operator_function (r) == boolean_true_node
	  || eval_is_conversion_function (r) == boolean_true_node)
	return boolean_false_node;
      else
	return boolean_true_node;
    }
  if (eval_is_template (r) == boolean_true_node)
    {
      if (eval_is_constructor_template (r) == boolean_true_node
	  || eval_is_operator_function_template (r) == boolean_true_node
	  || eval_is_conversion_function_template (r) == boolean_true_node)
	return boolean_false_node;
      else
	return boolean_true_node;
    }
  if (eval_is_function_parameter (r, kind) == boolean_true_node)
    {
      r = maybe_update_function_parm (r);
      if (MULTIPLE_NAMES_PARM_P (r))
	return boolean_false_node;
      if (DECL_NAME (r))
	{
	  if (strchr (IDENTIFIER_POINTER (DECL_NAME (r)), '#'))
	    return boolean_false_node;
	  else
	    return boolean_true_node;
	}
      if (lookup_attribute ("old parm name", DECL_ATTRIBUTES (r)))
	return boolean_true_node;
      else
	return boolean_false_node;
    }
  if (eval_is_variable (r, kind) == boolean_true_node)
    {
      if (strchr (IDENTIFIER_POINTER (DECL_NAME (r)), '#'))
	return boolean_false_node;
      if (eval_has_template_arguments (r) == boolean_true_node)
	return boolean_false_node;
      else
	return boolean_true_node;
    }
  if (eval_is_structured_binding (r) == boolean_true_node)
    {
      if (strchr (IDENTIFIER_POINTER (DECL_NAME (r)), '#'))
	return boolean_false_node;
      else
	return boolean_true_node;
    }
  if (eval_is_type_alias (r) == boolean_true_node)
    {
      if (eval_has_template_arguments (r) == boolean_true_node)
	return boolean_false_node;
      else
	return boolean_true_node;
    }
  if (eval_is_enumerator (r) == boolean_true_node
      || TREE_CODE (r) == FIELD_DECL
      || (TREE_CODE (r) == NAMESPACE_DECL && r != global_namespace))
    return boolean_true_node;
  // TODO: direct base class relationship.
  if (kind == REFLECT_DATA_MEMBER_SPEC && TREE_VEC_ELT (r, 1))
    return boolean_true_node;
  return boolean_false_node;
}

/* Process std::meta::{,u8}identifier_of.
   Let E be UTF-8 for u8identifier_of, and otherwise the ordinary literal
   encoding.
   Returns: An NTMBS, encoded with E, determined as follows:
   -- If r represents an entity with a typedef name for linkage purposes,
      then that name.
   -- Otherwise, if r represents a literal operator or literal operator
      template, then the ud-suffix of the operator or operator template.
   -- Otherwise, if r represents the parameter P of a function F, then let S
      be the set of declarations, ignoring any explicit instantiations, that
      precede some point in the evaluation context and that declare either F
      or a templated function of which F is a specialization; the name that
      was introduced by a declaration in S for the parameter corresponding
      to P.
   -- Otherwise, if r represents an entity, then the identifier introduced by
      the declaration of that entity.
   -- Otherwise, if r represents a direct base class relationship, then
      identifier_of(type_of(r)) or u8identifier_of(type_of(r)), respectively.
   -- Otherwise, r represents a data member description (T,N,A,W,NUA);
      a string_view or u8string_view, respectively, containing the identifier
      N.
   Throws: meta::exception unless has_identifier(r) is true and the identifier
   that would be returned (see above) is representable by E.  */

static tree
eval_identifier_of (location_t loc, const constexpr_ctx *ctx, tree r,
		    reflect_kind kind, tree *jump_target,
		    tree elt_type, tree ret_type)
{
  if (eval_has_identifier (r, kind) == boolean_false_node)
    return throw_exception (loc, ctx, N_("reflection with has_identifier "
					 "false"),
			    r, jump_target);
  r = MAYBE_BASELINK_FUNCTIONS (r);
  r = OVL_FIRST (r);
  const char *name = NULL;
  if (eval_is_function_parameter (r, kind) == boolean_true_node)
    {
      r = maybe_update_function_parm (r);
      if (DECL_NAME (r))
	name = IDENTIFIER_POINTER (DECL_NAME (r));
      else
	{
	  tree opn = lookup_attribute ("old parm name", DECL_ATTRIBUTES (r));
	  opn = TREE_VALUE (TREE_VALUE (opn));
	  name = IDENTIFIER_POINTER (opn);
	}
    }
  else if (DECL_P (r) && UDLIT_OPER_P (DECL_NAME (r)))
    name = UDLIT_OP_SUFFIX (DECL_NAME (r));
  else if (DECL_P (r))
    name = IDENTIFIER_POINTER (DECL_NAME (r));
  else if (TYPE_P (r))
    {
      if (DECL_P (TYPE_NAME (r)))
	name = IDENTIFIER_POINTER (DECL_NAME (TYPE_NAME (r)));
      else
	name = IDENTIFIER_POINTER (TYPE_NAME (r));
    }
  // TODO: direct base class relationship.
  else if (kind == REFLECT_DATA_MEMBER_SPEC)
    name = IDENTIFIER_POINTER (TREE_VEC_ELT (r, 1));
  else
    gcc_unreachable ();
  tree str = temp_string_literal (name, elt_type);
  if (str == NULL_TREE)
    {
      if (elt_type == char_type_node)
	return throw_exception (loc, ctx, N_("identifier_of not representable"
					     " in ordinary literal encoding"),
				r, jump_target);
      else
	return throw_exception (loc, ctx, N_("u8identifier_of not representable"
					     " in UTF-8"),
				r, jump_target);
    }
  releasing_vec args (make_tree_vector_single (str));
  tree ret = build_special_member_call (NULL_TREE, complete_ctor_identifier,
					&args, ret_type, LOOKUP_NORMAL,
					tf_warning_or_error);
  return build_cplus_new (ret_type, ret, tf_warning_or_error);
}

/* Determine the reflection kind for R.  */

static reflect_kind
get_reflection_kind (tree r)
{
  if (eval_is_type (r) == boolean_true_node
      || eval_is_template (r) == boolean_true_node)
    return REFLECT_UNDEF;
  return obvalue_p (r) ? REFLECT_OBJECT : REFLECT_VALUE;
}

/* Get the reflection of template argument ARG as per
   std::meta::template_arguments_of.  */

static tree
get_reflection_of_targ (tree arg)
{
  const location_t loc = location_of (arg);
  /* canonicalize_type_argument already strip_typedefs.  */
  arg = STRIP_REFERENCE_REF (arg);
  return get_reflection_raw (loc, arg, get_reflection_kind (arg));
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
  if (elts)
    {
      /* Reverse the order.  */
      unsigned l = elts->length ();
      constructor_elt *ptr = elts->address ();

      for (unsigned i = 0; i < l / 2; i++)
	std::swap (ptr[i], ptr[l - i - 1]);
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
eval_reflect_constant (location_t loc, const constexpr_ctx *ctx, tree type,
		       tree expr, tree *jump_target)
{
  if (!structural_type_p (type)
      || CP_TYPE_VOLATILE_P (type)
      || CP_TYPE_CONST_P (type)
      || TYPE_REF_P (type))
    {
      error_at (loc, "%qT must be a cv-unqualified structural type that is "
		"not a reference type", type);
      return error_mark_node;
    }
  expr = convert_reflect_constant_arg (type, convert_from_reference (expr));
  if (expr == error_mark_node)
    throw_exception_generic (loc, ctx, type, jump_target);
  return get_reflection_raw (loc, expr, get_reflection_kind (expr));
}

/* Process std::meta::reflect_object.
   Mandates: T is an object type.
   Returns: A reflection of the object designated by expr.
   Throws: meta::exception unless expr is suitable for use as a constant
   template argument for a constant template parameter of type T&.  */

static tree
eval_reflect_object (location_t loc, const constexpr_ctx *ctx, tree type,
		     tree expr, tree *jump_target)
{
  if (eval_is_object_type (loc, ctx, type, jump_target) != boolean_true_node)
    {
      error_at (loc, "%qT must be an object type", TREE_TYPE (type));
      return error_mark_node;
    }
  type = cp_build_reference_type (type, /*rval=*/false);
  tree e = convert_reflect_constant_arg (type, convert_from_reference (expr));
  if (e == error_mark_node)
    throw_exception_generic (loc, ctx, type, jump_target);
  /* We got (const T &) &foo.  Get the referent, since we want the object
     designated by EXPR.  */
  STRIP_NOPS (expr);
  expr = TREE_OPERAND (expr, 0);
  return get_reflection_raw (loc, expr, REFLECT_OBJECT);
}

/* Process std::meta::reflect_function.
   Mandates: T is a function type.
   Returns: A reflection of the function designated by fn.
   Throws: meta::exception unless fn is suitable for use as a constant
   template argument for a constant template parameter of type T&.  */

static tree
eval_reflect_function (location_t loc, const constexpr_ctx *ctx, tree type,
		       tree expr, tree *jump_target)
{
  if (eval_is_function_type (loc, ctx, type, jump_target) != boolean_true_node)
    {
      error_at (loc, "%qT must be a function type", TREE_TYPE (type));
      return error_mark_node;
    }
  type = cp_build_reference_type (type, /*rval=*/false);
  tree e = convert_reflect_constant_arg (type, convert_from_reference (expr));
  if (e == error_mark_node)
    throw_exception_generic (loc, ctx, type, jump_target);
  /* We got (void (&<Ta885>) (void)) fn.  Get the function.  */
  STRIP_NOPS (expr);
  expr = TREE_OPERAND (expr, 0);
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
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (FUNC_OR_METHOD_TYPE_P (type))
    return boolean_true_node;
  else
    return boolean_false_node;
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

/* Process std::meta::is_constructible_type.  */

static tree
eval_is_constructible_type (location_t loc, const constexpr_ctx *ctx,
			    tree type, tree tvec, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (is_xible (INIT_EXPR, type, tvec))
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

/* Process std::meta::is_trivially_constructible_type.  */

static tree
eval_is_trivially_constructible_type (location_t loc, const constexpr_ctx *ctx,
				      tree type, tree tvec, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (is_trivially_xible (INIT_EXPR, type, tvec))
    return boolean_true_node;
  else
    return boolean_false_node;
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

/* Process std::meta::is_nothrow_constructible_type.  */

static tree
eval_is_nothrow_constructible_type (location_t loc, const constexpr_ctx *ctx,
				    tree type, tree tvec, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (is_nothrow_xible (INIT_EXPR, type, tvec))
    return boolean_true_node;
  else
    return boolean_false_node;
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

/* Process std::meta::is_invocable_type.  */

static tree
eval_is_invocable_type (location_t loc, const constexpr_ctx *ctx,
			tree type, tree tvec, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree r = finish_trait_expr (input_location, CPTK_IS_INVOCABLE, type, tvec);
  STRIP_ANY_LOCATION_WRAPPER (r);
  return r;
}

/* Process std::meta::is_{,nothrow_}invocable_r_type.  */

static tree
eval_is_invocable_r_type (location_t loc, const constexpr_ctx *ctx,
			  tree tres, tree type, tree tvec, tree call,
			  bool *non_constant_p, tree *jump_target,
			  const char *name)
{
  if (eval_is_type (tres) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, tres, jump_target);
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);

  /* Create std::is_invocable_r<TYPE>::value.  */
  tree args = make_tree_vec (TREE_VEC_LENGTH (tvec) + 2);
  TREE_VEC_ELT (args, 0) = tres;
  TREE_VEC_ELT (args, 1) = type;
  for (int i = 0; i < TREE_VEC_LENGTH (tvec); ++i)
    TREE_VEC_ELT (args, i + 2) = TREE_VEC_ELT (tvec, i);
  tree inst = lookup_template_class (get_identifier (name), args,
				     /*in_decl*/NULL_TREE, /*context*/std_node,
				     tf_warning_or_error);
  inst = complete_type (inst);
  if (inst == error_mark_node
      || !COMPLETE_TYPE_P (inst)
      || !CLASS_TYPE_P (inst))
    {
    fail:
      if (!cxx_constexpr_quiet_p (ctx))
	error_at (loc, "couldn%'t evaluate %<std::%s<%T>::value%>",
		  name, args);
      *non_constant_p = true;
      return call;
    }
  tree val = lookup_qualified_name (inst, value_identifier,
				    LOOK_want::NORMAL, /*complain*/true);
  if (val == error_mark_node)
    goto fail;
  if (VAR_P (val) || TREE_CODE (val) == CONST_DECL)
    val = maybe_constant_value (val, NULL_TREE, mce_true);
  if (integer_zerop (val))
    return boolean_false_node;
  else if (integer_nonzerop (val))
    return boolean_true_node;
  else
    goto fail;
}

/* Process std::meta::is_nothrow_invocable_type.  */

static tree
eval_is_nothrow_invocable_type (location_t loc, const constexpr_ctx *ctx,
				tree type, tree tvec, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  tree r = finish_trait_expr (input_location, CPTK_IS_NOTHROW_INVOCABLE,
			      type, tvec);
  STRIP_ANY_LOCATION_WRAPPER (r);
  return r;
}

/* Process std::meta::remove_cvref.  */

static tree
eval_remove_cvref (location_t loc, const constexpr_ctx *ctx, tree type,
		   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  if (TYPE_REF_P (type))
    type = TREE_TYPE (type);
  type = finish_trait_type (CPTK_REMOVE_CV, type, NULL_TREE, tf_none);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::decay.  */

static tree
eval_decay (location_t loc, const constexpr_ctx *ctx, tree type,
	    tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = finish_trait_type (CPTK_DECAY, type, NULL_TREE, tf_none);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::common_{type,reference}.  */

static tree
eval_common_type (location_t loc, const constexpr_ctx *ctx, tree tvec,
		  tree call, bool *non_constant_p, const char *name)
{
  tree inst = lookup_template_class (get_identifier (name), tvec,
				     /*in_decl*/NULL_TREE,
				     /*context*/std_node,
				     tf_warning_or_error);
  tree type = make_typename_type (inst, type_identifier,
				  none_type, tf_warning_or_error);
  if (type == error_mark_node)
    {
      if (!cxx_constexpr_quiet_p (ctx))
	error_at (loc, "couldn%'t evaluate %<std::%s<%T>::type%>",
		  name, tvec);
      *non_constant_p = true;
      return call;
    }
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::underlying_type.  */

static tree
eval_underlying_type (location_t loc, const constexpr_ctx *ctx, tree type,
		      tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  /* The standard doesn't say this, but I hope it will clarify it.  */
  if (TREE_CODE (type) != ENUMERAL_TYPE || !COMPLETE_TYPE_P (type))
    return throw_exception (loc, ctx, N_("reflection does not represent "
					 "a complete enumeration type"),
			    type, jump_target);
  type = finish_underlying_type (type);
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::invoke_result.  */

static tree
eval_invoke_result (location_t loc, const constexpr_ctx *ctx, tree type,
		    tree tvec, tree call, bool *non_constant_p,
		    tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);

  tree args = make_tree_vec (TREE_VEC_LENGTH (tvec) + 1);
  TREE_VEC_ELT (args, 0) = type;
  for (int i = 0; i < TREE_VEC_LENGTH (tvec); ++i)
    TREE_VEC_ELT (args, i + 1) = TREE_VEC_ELT (tvec, i);
  tree inst = lookup_template_class (get_identifier ("invoke_result"), args,
				     /*in_decl*/NULL_TREE,
				     /*context*/std_node,
				     tf_warning_or_error);
  tree tret = make_typename_type (inst, type_identifier,
				  none_type, tf_warning_or_error);
  if (tret == error_mark_node)
    {
      if (!cxx_constexpr_quiet_p (ctx))
	error_at (loc, "couldn%'t evaluate %<std::%s<%T>::type%>",
		  "invoke_result", args);
      *non_constant_p = true;
      return call;
    }
  tret = strip_typedefs (tret);
  return get_reflection_raw (loc, tret);
}

/* Process std::meta::type_order.  */

static tree
eval_type_order (location_t loc, const constexpr_ctx *ctx, tree type1,
		 tree type2, tree *jump_target)
{
  if (eval_is_type (type1) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type1, jump_target);
  if (eval_is_type (type2) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type2, jump_target);
  return type_order_value (strip_typedefs (type1), strip_typedefs (type2));
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

/* Process std::meta::is_lvalue_reference_qualified and
   std::meta::is_rvalue_reference_qualified.
   Let T be type_of(r) if has-type(r) is true.  Otherwise, let T be
   dealias(r).
   Returns: true if T represents an lvalue- or rvalue-qualified
   function type, respectively.  Otherwise, false.
   RVALUE_P is true if we're processing is_rvalue_*, false if we're
   processing is_lvalue_*.  */

static tree
eval_is_lrvalue_reference_qualified (tree r, reflect_kind kind,
				     bool rvalue_p)
{
  if (has_type (r, kind))
    r = type_of (r, kind);
  else if (TYPE_P (r) && typedef_variant_p (r))
    r = strip_typedefs (r);
  if (FUNC_OR_METHOD_TYPE_P (r) && FUNCTION_REF_QUALIFIED (r))
    if (rvalue_p == FUNCTION_RVALUE_QUALIFIED (r))
      return boolean_true_node;

  return boolean_false_node;
}

/* Process std::meta::can_substitute.
   Let Z be the template represented by templ and let Args... be a sequence of
   prvalue constant expressions that compute the reflections held by the
   elements of arguments, in order.
   Returns: true if Z<[:Args:]...> is a valid template-id that does not name
   a function whose type contains an undeduced placeholder type.
   Otherwise, false.
   Throws: meta::exception unless templ represents a template, and every
   reflection in arguments represents a construct usable as a template
   argument.  */

static tree
eval_can_substitute (location_t loc, const constexpr_ctx *ctx,
		     tree r, tree rvec, tree *jump_target)
{
  if (eval_is_template (r) != boolean_true_node)
    return throw_exception (loc, ctx,
			    N_("reflection does not represent a template"),
			    r, jump_target);
  for (int i = 0; i < TREE_VEC_LENGTH (rvec); ++i)
    {
      tree ra = TREE_VEC_ELT (rvec, i);
      tree a = REFLECT_EXPR_HANDLE (ra);
      auto kind = static_cast<reflect_kind> (REFLECT_EXPR_KIND (ra));
      // TODO: It is unclear on what kinds of reflections we should throw
      // and what kinds of exceptions should merely result in can_substitute
      // returning false.  Direct base class relationship?
      if (a == unknown_type_node
	  || kind == REFLECT_PARM
	  || eval_is_namespace (a) == boolean_true_node
	  || eval_is_constructor (a) == boolean_true_node
	  || eval_is_destructor (a) == boolean_true_node
	  || eval_is_annotation (a) == boolean_true_node
	  || (TREE_CODE (a) == FIELD_DECL && !DECL_UNNAMED_BIT_FIELD (a))
	  || kind == REFLECT_DATA_MEMBER_SPEC)
	return throw_exception (loc, ctx,
				N_("invalid argument to can_substitute"),
				a, jump_target);
      else if (!TYPE_P (a) && eval_is_template (a) == boolean_false_node)
	{
	  if (!has_type (a, kind))
	    return throw_exception (loc, ctx,
				    N_("invalid argument to can_substitute"),
				    a, jump_target);
	}
      a = resolve_nondeduced_context (a, tf_warning_or_error);
      TREE_VEC_ELT (rvec, i) = a;
    }
  if (DECL_TYPE_TEMPLATE_P (r) || DECL_TEMPLATE_TEMPLATE_PARM_P (r))
    {
      tree type = lookup_template_class (r, rvec, NULL_TREE, NULL_TREE,
					 tf_none);
      if (type == error_mark_node)
	return boolean_false_node;
      else
	return boolean_true_node;
    }
  else if (concept_definition_p (r))
    {
      tree c = build_concept_check (r, rvec, tf_none);
      if (c == error_mark_node)
	return boolean_false_node;
      else
	return boolean_true_node;
    }
  else if (variable_template_p (r))
    {
      tree var = lookup_template_variable (r, rvec, tf_none);
      if (var == error_mark_node)
	return boolean_false_node;
      var = finish_template_variable (var, tf_none);
      if (var == error_mark_node)
	return boolean_false_node;
      else
	return boolean_true_node;
    }
  else
    {
      tree fn = lookup_template_function (r, rvec);
      if (fn == error_mark_node)
	return boolean_false_node;
      fn = resolve_nondeduced_context_or_error (fn, tf_none);
      if (fn == error_mark_node)
	return boolean_false_node;
      return boolean_true_node;
    }
}

/* Process std::meta::substitute.
   Let Z be the template represented by templ and let Args... be a sequence of
   prvalue constant expressions that compute the reflections held by the
   elements of arguments, in order.
   Returns: ^^Z<[:Args:]...>.
   Throws: meta::exception unless can_substitute(templ, arguments) is true.  */

static tree
eval_substitute (location_t loc, const constexpr_ctx *ctx,
		 tree r, tree rvec, tree *jump_target)
{
  tree cs = eval_can_substitute (loc, ctx, r, rvec, jump_target);
  if (*jump_target)
    return cs;
  if (cs == boolean_false_node)
    return throw_exception (loc, ctx,
			    N_("can_substitute returned false"),
			    r, jump_target);
  tree ret = NULL_TREE;
  if (DECL_TYPE_TEMPLATE_P (r) || DECL_TEMPLATE_TEMPLATE_PARM_P (r))
    ret = lookup_template_class (r, rvec, NULL_TREE, NULL_TREE, tf_none);
  else if (concept_definition_p (r))
    {
      ret = build_concept_check (r, rvec, tf_none);
      ret = evaluate_concept_check (ret);
      return get_reflection_raw (loc, ret, REFLECT_VALUE);
    }
  else if (variable_template_p (r))
    {
      ret = lookup_template_variable (r, rvec, tf_none);
      ret = finish_template_variable (ret, tf_none);
    }
  else
    ret = lookup_template_function (r, rvec);
  return get_reflection_raw (loc, ret);
}

/* Process std::meta::tuple_size.
   Returns: tuple_size_v<T>, where T is the type represented by
   dealias(type).  */

static tree
eval_tuple_size (location_t loc, const constexpr_ctx *ctx, tree type,
		 tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = strip_typedefs (type);
  /* It's UB to specialize tuple_size_v, so we can use this.  */
  return get_tuple_size (type);
}

/* Process std::meta::tuple_element.
   Returns: A reflection representing the type denoted by
   tuple_element_t<I, T>, where T is the type represented by dealias(type)
   and I is a constant equal to index.  */

static tree
eval_tuple_element (location_t loc, const constexpr_ctx *ctx, tree i,
		    tree type, tree *jump_target)
{
  const unsigned HOST_WIDE_INT index = tree_to_uhwi (i);
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = strip_typedefs (type);
  type = get_tuple_element_type (type, index);
  if (type == error_mark_node)
    return error_mark_node;
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::variant_size.
   Returns: variant_size_v<T>, where T is the type represented by
   dealias(type).  */

static tree
eval_variant_size (location_t loc, const constexpr_ctx *ctx, tree type,
		   tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = strip_typedefs (type);

  /* Create std::variant_size<TYPE>::value.  */
  tree args = make_tree_vec (1);
  TREE_VEC_ELT (args, 0) = type;
  tree inst = lookup_template_class (get_identifier ("variant_size"), args,
				     /*in_decl*/NULL_TREE, /*context*/std_node,
				     tf_warning_or_error);
  inst = complete_type (inst);
  if (inst == error_mark_node
      || !COMPLETE_TYPE_P (inst)
      || !CLASS_TYPE_P (inst))
    return NULL_TREE;
  tree val = lookup_qualified_name (inst, value_identifier,
				    LOOK_want::NORMAL, /*complain*/true);
  if (val == error_mark_node)
    return NULL_TREE;
  if (VAR_P (val) || TREE_CODE (val) == CONST_DECL)
    val = maybe_constant_value (val, NULL_TREE, mce_true);
  if (TREE_CODE (val) == INTEGER_CST)
    return val;
  else
    return NULL_TREE;
}

/* Process std::meta::variant_alternative.
   Returns: A reflection representing the type denoted by
   variant_alternative_t<I, T>, where T is the type represented by
   dealias(type) and I is a constant equal to index.  */

static tree
eval_variant_alternative (location_t loc, const constexpr_ctx *ctx, tree i,
			  tree type, tree *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = strip_typedefs (type);
  /* Create std::variant_alternative<I,TYPE>::type.  */
  tree args = make_tree_vec (2);
  TREE_VEC_ELT (args, 0) = i;
  TREE_VEC_ELT (args, 1) = type;
  tree inst = lookup_template_class (get_identifier ("variant_alternative"),
				     args, /*in_decl*/NULL_TREE,
				     /*context*/std_node,
				     tf_warning_or_error);
  type = make_typename_type (inst, type_identifier,
			     none_type, tf_warning_or_error);
  if (type == error_mark_node)
    return error_mark_node;
  type = strip_typedefs (type);
  return get_reflection_raw (loc, type);
}

/* Process std::meta::data_member_spec.
   Returns: A reflection of a data member description (T,N,A,W,NUA) where
   -- T is the type represented by dealias(type),
   -- N is either the identifier encoded by options.name or _|_ if
      options.name does not contain a value,
   -- A is either the alignment value held by options.alignment or _|_ if
      options.alignment does not contain a value,
   -- W is either the value held by options.bit_width or _|_ if
      options.bit_width does not contain a value, and
   -- NUA is the value held by options.no_unique_address.
   Throws: meta::exception unless the following conditions are met:
   -- dealias(type) represents either an object type or a reference type;
   -- if options.name contains a value, then:
      -- holds_alternative<u8string>(options.name->contents) is true and
	 get<u8string>(options.name->contents) contains a valid identifier
	 that is not a keyword when interpreted with UTF-8, or
      -- holds_alternative<string>(options.name->contents) is true and
	 get<string>(options.name->contents) contains a valid identifier
	 that is not a keyword when interpreted with the ordinary literal
	 encoding;
   -- if options.name does not contain a value, then options.bit_width
      contains a value;
   -- if options.bit_width contains a value V, then
      -- is_integral_type(type) || is_enum_type(type) is true,
      -- options.alignment does not contain a value,
      -- options.no_unique_address is false, and
      -- if V equals 0, then options.name does not contain a value; and
   -- if options.alignment contains a value, it is an alignment value not less
      than alignment_of(type).  */

static tree
eval_data_member_spec (location_t loc, const constexpr_ctx *ctx,
		       tree type, tree opts, tree call,
		       bool *non_constant_p, bool *overflow_p,
		       tree  *jump_target)
{
  if (eval_is_type (type) != boolean_true_node)
    return throw_exception_nontype (loc, ctx, type, jump_target);
  type = strip_typedefs (type);
  if (!TYPE_OBJ_P (type) && !TYPE_REF_P (type))
    return throw_exception (loc, ctx,
			    N_("type is not object or reference type"),
			    type, jump_target);
  opts = convert_from_reference (opts);
  if (!CLASS_TYPE_P (TREE_TYPE (opts)))
    {
    fail:
      error_at (loc, "unexpected %<data_member_options%> argument");
      *non_constant_p = true;
      return error_mark_node;
    }
  tree args[5] = { type, NULL_TREE, NULL_TREE, NULL_TREE, NULL_TREE };
  for (tree field = next_aggregate_field (TYPE_FIELDS (TREE_TYPE (opts)));
       field; field = next_aggregate_field (DECL_CHAIN (field)))
    if (tree name = DECL_NAME (field))
      {
	if (id_equal (name, "name"))
	  args[1] = field;
	else if (id_equal (name, "alignment"))
	  args[2] = field;
	else if (id_equal (name, "bit_width"))
	  args[3] = field;
	else if (id_equal (name, "no_unique_address"))
	  args[4] = field;
      }
  for (int i = 1; i < 5; ++i)
    {
      if (args[i] == NULL_TREE)
	goto fail;
      tree opt = build3 (COMPONENT_REF, TREE_TYPE (args[i]), opts, args[i],
			 NULL_TREE);
      if (i == 4)
	{
	  /* The no_unique_address handling is simple.  */
	  if (TREE_CODE (TREE_TYPE (opt)) != BOOLEAN_TYPE)
	    goto fail;
	  opt = cxx_eval_constant_expression (ctx, opt, vc_prvalue,
					      non_constant_p, overflow_p,
					      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  if (TREE_CODE (opt) != INTEGER_CST)
	    goto fail;
	  if (integer_zerop (opt))
	    args[i] = boolean_false_node;
	  else
	    args[i] = boolean_true_node;
	  continue;
	}
      /* Otherwise the member is optional<something>.  */
      if (!CLASS_TYPE_P (TREE_TYPE (opt)))
	goto fail;
      tree has_value = build_static_cast (loc, boolean_type_node, opt,
					  tf_warning_or_error);
      if (error_operand_p (has_value))
	goto fail;
      has_value = cxx_eval_constant_expression (ctx, has_value, vc_prvalue,
						non_constant_p, overflow_p,
						jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      if (TREE_CODE (has_value) != INTEGER_CST)
	goto fail;
      if (integer_zerop (has_value))
	{
	  /* If it doesn't have value, store NULL_TREE.  */
	  args[i] = NULL_TREE;
	  continue;
	}
      tree deref = build_new_op (loc, INDIRECT_REF, LOOKUP_NORMAL, opt,
				 NULL_TREE, tf_warning_or_error);
      if (error_operand_p (deref))
	goto fail;
      if (i != 1)
	{
	  /* For alignment and bit_width otherwise it should be int.  */
	  if (TYPE_MAIN_VARIANT (TREE_TYPE (deref)) != integer_type_node)
	    goto fail;
	  deref = cxx_eval_constant_expression (ctx, deref, vc_prvalue,
						non_constant_p, overflow_p,
						jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  if (TREE_CODE (deref) != INTEGER_CST)
	    goto fail;
	  args[i] = deref;
	  continue;
	}
      /* Otherwise it is a name.  */
      if (!CLASS_TYPE_P (TREE_TYPE (deref)))
	goto fail;
      tree fields[3] = { NULL_TREE, NULL_TREE, NULL_TREE };
      for (tree field = next_aggregate_field (TYPE_FIELDS (TREE_TYPE (deref)));
	   field; field = next_aggregate_field (DECL_CHAIN (field)))
	if (tree name = DECL_NAME (field))
	  {
	    if (id_equal (name, "_M_is_u8"))
	      fields[0] = field;
	    else if (id_equal (name, "_M_u8s"))
	      fields[1] = field;
	    else if (id_equal (name, "_M_s"))
	      fields[2] = field;
	  }
      for (int j = 0; j < 3; ++j)
	{
	  if (fields[j] == NULL_TREE)
	    goto fail;
	  if (j && j == (fields[0] == boolean_true_node ? 2 : 1))
	    continue;
	  tree f = build3 (COMPONENT_REF, TREE_TYPE (fields[j]), deref,
			   fields[j], NULL_TREE);
	  if (j == 0)
	    {
	      /* The _M_is_u8 handling is simple.  */
	      if (TREE_CODE (TREE_TYPE (f)) != BOOLEAN_TYPE)
		goto fail;
	      f = cxx_eval_constant_expression (ctx, f, vc_prvalue,
						non_constant_p, overflow_p,
						jump_target);
	      if (*jump_target)
		return NULL_TREE;
	      if (*non_constant_p)
		return call;
	      if (TREE_CODE (f) != INTEGER_CST)
		goto fail;
	      if (integer_zerop (f))
		fields[0] = boolean_false_node;
	      else
		fields[0] = boolean_true_node;
	      continue;
	    }
	  /* _M_u8s/_M_s handling is the same except for encoding.  */
	  if (!CLASS_TYPE_P (TREE_TYPE (f)))
	    goto fail;
	  tree fns = lookup_qualified_name (TREE_TYPE (f),
					    get_identifier ("c_str"));
	  if (error_operand_p (fns))
	    goto fail;
	  f = build_new_method_call (f, fns, NULL, NULL_TREE, LOOKUP_NORMAL,
				     NULL, tf_warning_or_error);
	  if (error_operand_p (f))
	    goto fail;
	  f = cxx_eval_constant_expression (ctx, f, vc_prvalue,
					    non_constant_p, overflow_p,
					    jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  STRIP_NOPS (f);
	  if (TREE_CODE (f) != ADDR_EXPR)
	    goto fail;
	  f = TREE_OPERAND (f, 0);
	  f = cxx_eval_constant_expression (ctx, f, vc_prvalue,
					    non_constant_p, overflow_p,
					    jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  if (TREE_CODE (f) != CONSTRUCTOR
	      || TREE_CODE (TREE_TYPE (f)) != ARRAY_TYPE)
	    goto fail;
	  tree eltt = TYPE_MAIN_VARIANT (TREE_TYPE (TREE_TYPE (f)));
	  if (eltt != (j == 1 ? char8_type_node : char_type_node))
	    goto fail;
	  tree field, value;
	  unsigned k;
	  unsigned HOST_WIDE_INT l = 0;
	  bool ntmbs = false;
	  FOR_EACH_CONSTRUCTOR_ELT (CONSTRUCTOR_ELTS (f), k, field, value)
	    if (!tree_fits_shwi_p (value))
	      goto fail;
	    else if (field == NULL_TREE)
	      {
		if (integer_zerop (value))
		  {
		    ntmbs = true;
		    break;
		  }
		++l;
	      }
	    else if (TREE_CODE (field) == RANGE_EXPR)
	      {
		tree lo = TREE_OPERAND (field, 0);
		tree hi = TREE_OPERAND (field, 1);
		if (!tree_fits_uhwi_p (lo) || !tree_fits_uhwi_p (hi))
		  goto fail;
		if (integer_zerop (value))
		  {
		    l = tree_to_uhwi (lo);
		    ntmbs = true;
		    break;
		  }
		l = tree_to_uhwi (hi) + 1;
	      }
	    else if (tree_fits_uhwi_p (field))
	      {
		l = tree_to_uhwi (field);
		if (integer_zerop (value))
		  {
		    ntmbs = true;
		    break;
		  }
		++l;
	      }
	    else
	      goto fail;
	  if (!ntmbs || l > INT_MAX - 1)
	    goto fail;
	  char *namep;
	  unsigned len = l;
	  if (l < 64)
	    namep = XALLOCAVEC (char, l + 1);
	  else
	    namep = XNEWVEC (char, l + 1);
	  memset (namep, 0, l + 1);
	  l = 0;
	  FOR_EACH_CONSTRUCTOR_ELT (CONSTRUCTOR_ELTS (f), k, field, value)
	    if (field == NULL_TREE)
	      {
		if (integer_zerop (value))
		  break;
		namep[l] = tree_to_shwi (value);
		++l;
	      }
	    else if (TREE_CODE (field) == RANGE_EXPR)
	      {
		tree lo = TREE_OPERAND (field, 0);
		tree hi = TREE_OPERAND (field, 1);
		if (integer_zerop (value))
		  break;
		unsigned HOST_WIDE_INT m = tree_to_uhwi (hi);
		for (l = tree_to_uhwi (lo); l <= m; ++l)
		  namep[l] = tree_to_shwi (value);
	      }
	    else
	      {
		l = tree_to_uhwi (field);
		namep[l++] = tree_to_shwi (value);
	      }
	  namep[len] = '\0';
	  /* Convert namep from execution charset to SOURCE_CHARSET.  */
	  cpp_string istr, ostr;
	  istr.len = strlen (namep) + 1;
	  istr.text = (const unsigned char *) namep;
	  if (!cpp_translate_string (parse_in, &istr, &ostr,
				     j == 2 ? CPP_STRING : CPP_UTF8STRING,
				     true))
	    {
	      if (len >= 64)
		XDELETEVEC (namep);
	      if (j == 1)
		return throw_exception (loc, ctx,
					N_("conversion from ordinary literal "
					   "encoding to source charset "
					   "failed"),
					type, jump_target);
	      else
		return throw_exception (loc, ctx,
					N_("conversion from UTF-8 encoding to "
					   "source charset failed"),
					type, jump_target);
	    }
	  if (len >= 64)
	    XDELETEVEC (namep);
	  if (!cpp_valid_identifier (parse_in, ostr.text))
	    return throw_exception (loc, ctx,
				    N_("name is not a valid identifier"),
				    type, jump_target);
	  args[i] = get_identifier ((const char *) ostr.text);
	  switch (get_identifier_kind (args[i]))
	    {
	    case cik_keyword:
	      return throw_exception (loc, ctx,
				      N_("name is a keyword"),
				      type, jump_target);
	    case cik_trait:
	      return throw_exception (loc, ctx,
				      N_("name is a built-in trait"),
				      type, jump_target);
	    default:
	      break;
	    }
	}
    }
  if (args[1] == NULL_TREE && args[3] == NULL_TREE)
    return throw_exception (loc, ctx,
			    N_("neither name nor bit_width specified"),
			    type, jump_target);
  if (args[3])
    {
      if (!CP_INTEGRAL_TYPE_P (type) && TREE_CODE (type) != ENUMERAL_TYPE)
	return throw_exception (loc, ctx,
				N_("bit_width specified with non-integral "
				   "and non-enumeration type"),
				type, jump_target);
      if (args[2])
	return throw_exception (loc, ctx,
				N_("both alignment and bit_width specified"),
				type, jump_target);
      if (args[4] == boolean_true_node)
	return throw_exception (loc, ctx,
				N_("bit_width specified with "
				   "no_unique_address true"),
				type, jump_target);
      if (integer_zerop (args[3]) && args[1])
	return throw_exception (loc, ctx,
				N_("bit_width 0 with specified name"),
				type, jump_target);
      if (tree_int_cst_sgn (args[3]) < 0)
	return throw_exception (loc, ctx, N_("bit_width is negative"),
				type, jump_target);
    }
  if (args[2])
    {
      if (!integer_pow2p (args[2]))
	return throw_exception (loc, ctx,
				N_("alignment is not power of two"),
				type, jump_target);
      if (tree_int_cst_sgn (args[2]) < 0)
	return throw_exception (loc, ctx, N_("alignment is negative"),
				type, jump_target);
      tree al = cxx_sizeof_or_alignof_type (loc, type, ALIGNOF_EXPR, true,
					    tf_none);
      if (TREE_CODE (al) == INTEGER_CST
	  && wi::to_widest (al) > wi::to_widest (args[2]))
	return throw_exception (loc, ctx,
				N_("alignment is smaller than alignment_of"),
				type, jump_target);
    }
  tree ret = make_tree_vec (5);
  for (int i = 0; i < 5; ++i)
    TREE_VEC_ELT (ret, i) = args[i];
  return get_reflection_raw (loc, ret, REFLECT_DATA_MEMBER_SPEC);
}

/* Process std::meta::define_aggregate.
   Let C be the class represented by class_type and r_K be the Kth reflection
   value in mdescrs.
   For every r_K in mdescrs, let (T_K,N_K,A_K,W_K,NUA_K) be the corresponding
   data member description represented by r_K.
   Constant When:
   -- C is incomplete from every point in the evaluation context;
   -- is_data_member_spec(r_K) is true for every r_K;
   -- is_complete_type(T_K) is true for every r_K; and
   -- for every pair (r_K,r_L) where K<L, if N_K is not _|_ and N_L is not
      _|_, then either:
      -- N_K != N_L is true or
      -- N_K == u8"_" is true.
   Effects: Produces an injected declaration D that defines C and has
   properties as follows:
   -- The target scope of D is the scope to which C belongs.
   -- The locus of D follows immediately after the core constant expression
      currently under evaluation.
   -- The characteristic sequence of D is the sequence of reflection values
      r_K.
   -- If C is a specialization of a templated class T, and C is not a local
      class, then D is an explicit specialization of T.
   -- For each r_K, there is a corresponding entity M_K belonging to the class
      scope of D with the following properties:
      -- If N_K is _|_, M_K is an unnamed bit-field.
	 Otherwise, M_K is a non-static data member whose name is the
	 determined by the character sequence encoded by N_K in UTF-8.
      -- The type of M_K is T_K.
      -- M_K is declared with the attribute [[no_unique_address]] if and only
	 if NUA_K is true.
      -- If W_K is not _|_, M_K is a bit-field whose width is that value.
	 Otherwise, M_K is not a bit-field.
      -- If A_K is not _|_, M_K has the alignment-specifier alignas(A_K).
	 Otherwise, M_K has no alignment-specifier.
   -- For every r_L in mdescrs such that K<L, the declaration corresponding to
      r_K precedes the declaration corresponding to r_L.
   Returns: class_type.  */

static tree
eval_define_aggregate (location_t loc, const constexpr_ctx *ctx,
		       tree type, tree rvec, tree call, bool *non_constant_p)
{
  tree orig_type = type;
  if (!CLASS_TYPE_P (type))
    {
      if (!cxx_constexpr_quiet_p (ctx))
	error_at (loc, "first %<define_aggregate%> argument is not a class "
		       "type reflection");
      *non_constant_p = true;
      return call;
    }
  if (COMPLETE_TYPE_P (type))
    {
      if (!cxx_constexpr_quiet_p (ctx))
	error_at (loc, "first %<define_aggregate%> argument is a complete "
		       "class type reflection");
      *non_constant_p = true;
      return call;
    }
  hash_set<tree> nameset;
  for (int i = 0; i < TREE_VEC_LENGTH (rvec); ++i)
    {
      tree ra = TREE_VEC_ELT (rvec, i);
      tree a = REFLECT_EXPR_HANDLE (ra);
      if (REFLECT_EXPR_KIND (ra) != REFLECT_DATA_MEMBER_SPEC)
	{
	  if (!cxx_constexpr_quiet_p (ctx))
	    error_at (loc, "%<define_aggregate%> argument not a data member "
			   "description");
	  *non_constant_p = true;
	  return call;
	}
      if (eval_is_complete_type (TREE_VEC_ELT (a, 0)) != boolean_true_node)
	{
	  if (!cxx_constexpr_quiet_p (ctx))
	    error_at (loc, "%<define_aggregate%> argument data member "
			   "description without complete type");
	  *non_constant_p = true;
	  return call;
	}
      if (TREE_VEC_ELT (a, 1)
	  && !id_equal (TREE_VEC_ELT (a, 1), "_")
	  && nameset.add (TREE_VEC_ELT (a, 1)))
	{
	  if (!cxx_constexpr_quiet_p (ctx))
	    error_at (loc, "name %qD used in multiple data member "
			   "descriptions", TREE_VEC_ELT (a, 1));
	  *non_constant_p = true;
	  return call;
	}
      if (TYPE_WARN_IF_NOT_ALIGN (type)
	  && TREE_VEC_ELT (a, 3))
	{
	  if (!cxx_constexpr_quiet_p (ctx))
	    error_at (loc, "cannot declare bit-field in "
			   "%<warn_if_not_aligned%> type");
	  *non_constant_p = true;
	  return call;
	}
    }
  if (cxx_constexpr_manifestly_const_eval (ctx) != mce_true)
    {
      /* If define_aggregate is evaluated multiple times,
	 the second invocation with the same arguments will
	 necessarily fail.  Limit those to manifestly
	 constant-evaluation.  */
      if (!cxx_constexpr_quiet_p (ctx))
	error_at (loc, "%<define_aggregate%> used outside of "
		       "manifestly constant-evaluation");
      *non_constant_p = true;
      return call;
    }
  iloc_sentinel ils = loc;
  type = strip_typedefs (type);
  type = TYPE_MAIN_VARIANT (type);
  if (primary_template_specialization_p (type))
    {
      type = maybe_process_partial_specialization (type);
      if (type == error_mark_node)
	{
	  *non_constant_p = true;
	  return call;
	}
    }
  if (!TYPE_BINFO (type))
    xref_basetypes (type, NULL_TREE);
  pushclass (type);
  gcc_assert (!TYPE_FIELDS (type));
  tree fields = NULL_TREE;
  for (int i = 0; i < TREE_VEC_LENGTH (rvec); ++i)
    {
      tree ra = TREE_VEC_ELT (rvec, i);
      tree a = REFLECT_EXPR_HANDLE (ra);
      tree f = build_decl (cp_expr_loc_or_input_loc (ra), FIELD_DECL,
			   TREE_VEC_ELT (a, 1), TREE_VEC_ELT (a, 0));
      DECL_CHAIN (f) = fields;
      DECL_IN_AGGR_P (f) = 1;
      DECL_CONTEXT (f) = type;
      TREE_PUBLIC (f) = 1;
      if (TREE_VEC_ELT (a, 3))
	{
	  /* Temporarily stash the width in DECL_BIT_FIELD_REPRESENTATIVE.
	     check_bitfield_decl picks it from there later and sets DECL_SIZE
	     accordingly.  */
	  DECL_BIT_FIELD_REPRESENTATIVE (f) = TREE_VEC_ELT (a, 3);
	  SET_DECL_C_BIT_FIELD (f);
	}
      else if (TREE_VEC_ELT (a, 2))
	{
	  SET_DECL_ALIGN (f, tree_to_uhwi (TREE_VEC_ELT (a, 2))
			      * BITS_PER_UNIT);
	  DECL_USER_ALIGN (f) = 1;
	}
      if (TREE_VEC_ELT (a, 4) == boolean_true_node)
	{
	  tree attr = build_tree_list (NULL_TREE,
				       get_identifier ("no_unique_address"));
	  attr = build_tree_list (attr, NULL_TREE);
	  cplus_decl_attributes (&f, attr, 0);
	}
      fields = f;
    }
  TYPE_FIELDS (type) = fields;
  finish_struct (type, NULL_TREE);
  return get_reflection_raw (loc, orig_type);
}

/* Implement std::meta::reflect_constant_string.
   Let CharT be ranges::range_value_t<R>.
   Mandates: CharT is one of char, wchar_t, char8_t, char16_t, char32_t.
   Let V be the pack of values of type CharT whose elements are the
   corresponding elements of r, except that if r refers to a string literal
   object, then V does not include the trailing null terminator of r.
   Let P be the template parameter object of type
   const CharT[sizeof...(V) + 1] initialized with {V..., CharT()}.
   Returns: ^^P.  */

static tree
eval_reflect_constant_string (location_t loc, const constexpr_ctx *ctx,
			      tree call, bool *non_constant_p,
			      bool *overflow_p, tree *jump_target)
{
  tree str = get_range_elts (loc, ctx, call, 0, non_constant_p, overflow_p,
			     jump_target, REFLECT_CONSTANT_STRING);
  if (*jump_target)
    return NULL_TREE;
  if (*non_constant_p)
    return call;
  tree decl = get_template_parm_object (str,
					mangle_template_parm_object (str));
  DECL_MERGEABLE (decl) = 1;
  return get_reflection_raw (loc, decl);
}

/* Implement std::meta::reflect_constant_array.
   Let T be ranges::range_value_t<R>.
   Mandates: T is a structural type,
   is_constructible_v<T, ranges::range_reference_t<R>> is true, and
   is_copy_constructible_v<T> is true.
   Let V be the pack of values of type info of the same size as r, where the
   ith element is reflect_constant(e_i), where e_i is the ith element of r.
   Let P be
   -- If sizeof...(V) > 0 is true, then the template parameter object of type
      const T[sizeof...(V)] initialized with {[:V:]...}.
   -- Otherwise, the template parameter object of type array<T, 0> initialized
      with {}.
   Returns: ^^P.  */

static tree
eval_reflect_constant_array (location_t loc, const constexpr_ctx *ctx,
			      tree call, bool *non_constant_p,
			      bool *overflow_p, tree *jump_target)
{
  tree str = get_range_elts (loc, ctx, call, 0, non_constant_p, overflow_p,
			     jump_target, REFLECT_CONSTANT_ARRAY);
  if (*jump_target)
    return NULL_TREE;
  if (*non_constant_p)
    return call;
  tree decl = get_template_parm_object (str,
					mangle_template_parm_object (str));
  DECL_MERGEABLE (decl) = 1;
  return get_reflection_raw (loc, decl);
}

/* Expand a call to a metafunction FUN.  CALL is the CALL_EXPR.
   JUMP_TARGET is set if we are throwing std::meta::exception.  */

// TODO Use gperf?
tree
process_metafunction (const constexpr_ctx *ctx, tree fun, tree call,
		      bool *non_constant_p, bool *overflow_p,
		      tree *jump_target)
{
  tree name = DECL_NAME (fun);
  const char *ident = IDENTIFIER_POINTER (name);
  const location_t loc = cp_expr_loc_or_input_loc (call);

  if (id_equal (name, "reflect_constant")
      || id_equal (name, "reflect_object")
      || id_equal (name, "reflect_function"))
    {
      tree expr = get_nth_callarg (call, 0);
      tree type = TREE_VEC_ELT (get_template_innermost_arguments (fun), 0);
      expr = cxx_eval_constant_expression (ctx, expr, vc_prvalue,
					   non_constant_p, overflow_p,
					   jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      if (id_equal (name, "reflect_constant"))
	return eval_reflect_constant (loc, ctx, type, expr, jump_target);
      else if (id_equal (name, "reflect_object"))
	return eval_reflect_object (loc, ctx, type, expr, jump_target);
      else
	return eval_reflect_function (loc, ctx, type, expr, jump_target);
    }
  if (id_equal (name, "symbol_of") || id_equal (name, "u8symbol_of"))
    {
      tree expr = get_nth_callarg (call, 0);
      expr = cxx_eval_constant_expression (ctx, expr, vc_prvalue,
					   non_constant_p, overflow_p,
					   jump_target);
      if (*jump_target)
	return NULL_TREE;
      return eval_symbol_of (loc, ctx, expr, jump_target,
			     id_equal (name, "symbol_of") ? char_type_node
			     : char8_type_node, TREE_TYPE (call));
    }
  if (id_equal (name, "tuple_element")
      || id_equal (name, "variant_alternative"))
    {
      tree i = get_nth_callarg (call, 0);
      i = cxx_eval_constant_expression (ctx, i, vc_prvalue,
					non_constant_p, overflow_p,
					jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      tree type = get_info (ctx, call, 1, non_constant_p, overflow_p,
			    jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      type = REFLECT_EXPR_HANDLE (type);
      if (id_equal (name, "tuple_element"))
	type = eval_tuple_element (loc, ctx, i, type, jump_target);
      else
	type = eval_variant_alternative (loc, ctx, i, type, jump_target);
      if (type == error_mark_node)
	{
	  *non_constant_p = true;
	  return call;
	}
      return type;
    }
  if (id_equal (name, "common_type") || id_equal (name, "common_reference"))
    {
      tree hvec = get_type_info_vec (loc, ctx, call, 0, non_constant_p,
				     overflow_p, jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      return eval_common_type (loc, ctx, hvec, call, non_constant_p, ident);
    }
  if (id_equal (name, "reflect_constant_string"))
    return eval_reflect_constant_string (loc, ctx, call, non_constant_p,
					 overflow_p, jump_target);
  if (id_equal (name, "reflect_constant_array"))
    return eval_reflect_constant_array (loc, ctx, call, non_constant_p,
					overflow_p, jump_target);

  tree info = get_info (ctx, call, 0, non_constant_p, overflow_p, jump_target);
  if (*jump_target)
    return NULL_TREE;
  if (*non_constant_p)
    return call;
  tree h = REFLECT_EXPR_HANDLE (info);
  auto kind = static_cast<reflect_kind>(REFLECT_EXPR_KIND (info));

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
      if (!strcmp (ident, "value"))
	return eval_is_value (kind);
      if (!strcmp (ident, "structured_binding"))
	return eval_is_structured_binding (h);
      if (!strcmp (ident, "class_member"))
	return eval_is_class_member (h);
      if (!strcmp (ident, "namespace_member"))
	return eval_is_namespace_member (h);
      if (!strcmp (ident, "nonstatic_data_member"))
	return eval_is_nonstatic_data_member (h);
      if (!strcmp (ident, "static_member"))
	return eval_is_static_member (h);
      if (!strcmp (ident, "mutable_member"))
	return eval_is_mutable_member (h);
      if (!strcmp (ident, "template"))
	return eval_is_template (h);
      if (!strcmp (ident, "function_parameter"))
	return eval_is_function_parameter (h, kind);
      if (!strcmp (ident, "explicit_object_parameter"))
	return eval_is_explicit_object_parameter (h, kind);
      if (!strcmp (ident, "deleted"))
	return eval_is_deleted (h);
      if (!strcmp (ident, "defaulted"))
	return eval_is_defaulted (h);
      if (!strcmp (ident, "user_provided"))
	return eval_is_user_provided (h);
      if (!strcmp (ident, "user_declared"))
	return eval_is_user_declared (h);
      if (!strcmp (ident, "explicit"))
	return eval_is_explicit (h);
      if (!strcmp (ident, "bit_field"))
	return eval_is_bit_field (h, kind);
      if (!strcmp (ident, "enumerator"))
	return eval_is_enumerator (h);
      if (!strcmp (ident, "complete_type"))
	return eval_is_complete_type (h);
      if (!strcmp (ident, "enumerable_type"))
	return eval_is_enumerable_type (h);
      if (!strcmp (ident, "annotation"))
	return eval_is_annotation (h);
      if (!strcmp (ident, "noexcept"))
	return eval_is_noexcept (loc, ctx, h, jump_target);
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
      if (!strcmp (ident, "operator_function_template"))
	return eval_is_operator_function_template (h);
      if (!strcmp (ident, "literal_operator_template"))
	return eval_is_literal_operator_template (h);
      if (!strcmp (ident, "constructor_template"))
	return eval_is_constructor_template (h);
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
      if (!strcmp (ident, "constructible_type"))
	{
	  tree hvec = get_type_info_vec (loc, ctx, call, 1, non_constant_p,
					 overflow_p, jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  return eval_is_constructible_type (loc, ctx, h, hvec, jump_target);
	}
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
      if (!strcmp (ident, "trivially_constructible_type"))
	{
	  tree hvec = get_type_info_vec (loc, ctx, call, 1, non_constant_p,
					 overflow_p, jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  return eval_is_trivially_constructible_type (loc, ctx, h, hvec,
						       jump_target);
	}
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
      if (!strcmp (ident, "nothrow_constructible_type"))
	{
	  tree hvec = get_type_info_vec (loc, ctx, call, 1, non_constant_p,
					 overflow_p, jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  return eval_is_nothrow_constructible_type (loc, ctx, h, hvec,
						     jump_target);
	}
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
      if (!strcmp (ident, "invocable_type"))
	{
	  tree hvec = get_type_info_vec (loc, ctx, call, 1, non_constant_p,
					 overflow_p, jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  return eval_is_invocable_type (loc, ctx, h, hvec, jump_target);
	}
      if (!strcmp (ident, "nothrow_invocable_type"))
	{
	  tree hvec = get_type_info_vec (loc, ctx, call, 1, non_constant_p,
					 overflow_p, jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  return eval_is_nothrow_invocable_type (loc, ctx, h, hvec,
						 jump_target);
	}
      if (!strcmp (ident, "invocable_r_type")
	  || !strcmp (ident, "nothrow_invocable_r_type"))
	{
	  tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			      jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  tree h1 = REFLECT_EXPR_HANDLE (i1);
	  tree hvec = get_type_info_vec (loc, ctx, call, 2, non_constant_p,
					 overflow_p, jump_target);
	  if (*jump_target)
	    return NULL_TREE;
	  if (*non_constant_p)
	    return call;
	  return eval_is_invocable_r_type (loc, ctx, h, h1, hvec, call,
					   non_constant_p, jump_target,
					   ident[0] == 'n'
					   ? "is_nothrow_invocable_r"
					   : "is_invocable_r");
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
      if (!strcmp (ident, "data_member_spec"))
	return eval_is_data_member_spec (h, kind);
      if (!strcmp (ident, "lvalue_reference_qualified"))
	return eval_is_lrvalue_reference_qualified (h, kind,
						    /*rvalue_p=*/false);
      if (!strcmp (ident, "rvalue_reference_qualified"))
	return eval_is_lrvalue_reference_qualified (h, kind,
						    /*rvalue_p=*/true);
      goto not_found;
    }

  /* Handle has_*.  */
  if (startswith (ident, "has_"))
    {
      ident += 4;
      if (!strcmp (ident, "identifier"))
	return eval_has_identifier (h, kind);
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
      if (!strcmp (ident, "default_argument"))
	return eval_has_default_argument (h, kind);
      if (!strcmp (ident, "ellipsis_parameter"))
	return eval_has_ellipsis_parameter (h);
      if (!strcmp (ident, "virtual_destructor"))
	return eval_has_virtual_destructor (loc, ctx, h, jump_target);
      if (!strcmp (ident, "unique_object_representations"))
	return eval_has_unique_object_representations (loc, ctx, h,
						       jump_target);
      if (!strcmp (ident, "default_member_initializer"))
	return eval_has_default_member_initializer (h);
      if (!strcmp (ident, "static_storage_duration"))
	return eval_has_static_storage_duration (h, kind);
      if (!strcmp (ident, "thread_storage_duration"))
	return eval_has_thread_storage_duration (h, kind);
      if (!strcmp (ident, "automatic_storage_duration"))
	return eval_has_automatic_storage_duration (h, kind);
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
      i = cxx_eval_constant_expression (ctx, i, vc_prvalue,
					non_constant_p, overflow_p,
					jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      return eval_extent (loc, ctx, h, i, jump_target);
    }
  if (id_equal (name, "remove_cvref"))
    return eval_remove_cvref (loc, ctx, h, jump_target);
  if (id_equal (name, "decay"))
    return eval_decay (loc, ctx, h, jump_target);
  if (id_equal (name, "underlying_type"))
    return eval_underlying_type (loc, ctx, h, jump_target);
  if (id_equal (name, "type_order"))
    {
      tree i1 = get_info (ctx, call, 1, non_constant_p, overflow_p,
			  jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      tree h1 = REFLECT_EXPR_HANDLE (i1);
      return eval_type_order (loc, ctx, h, h1, jump_target);
    }
  if (id_equal (name, "identifier_of"))
    return eval_identifier_of (loc, ctx, h, kind, jump_target, char_type_node,
			       TREE_TYPE (call));
  if (id_equal (name, "u8identifier_of"))
    return eval_identifier_of (loc, ctx, h, kind, jump_target,
			       char8_type_node, TREE_TYPE (call));
  if (id_equal (name, "tuple_size"))
    {
      tree tsize = eval_tuple_size (loc, ctx, h, jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (!tsize || tsize == error_mark_node)
	{
	  if (!cxx_constexpr_quiet_p (ctx))
	    error_at (loc, "couldn%'t compute %qs of %qT", "tuple_size", h);
	  *non_constant_p = true;
	  return call;
	}
      return tsize;
    }
  if (id_equal (name, "variant_size"))
    {
      tree tsize = eval_variant_size (loc, ctx, h, jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (!tsize)
	{
	  if (!cxx_constexpr_quiet_p (ctx))
	    error_at (loc, "couldn%'t compute %qs of %qT", "variant_size", h);
	  *non_constant_p = true;
	  return call;
	}
      return tsize;
    }
  if (!strcmp (ident, "invoke_result"))
    {
      tree hvec = get_type_info_vec (loc, ctx, call, 1, non_constant_p,
				     overflow_p, jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      return eval_invoke_result (loc, ctx, h, hvec, call,
				 non_constant_p, jump_target);
    }
  if (id_equal (name, "can_substitute"))
    {
      tree hvec = get_info_vec (loc, ctx, call, 1, non_constant_p,
				overflow_p, jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      return eval_can_substitute (loc, ctx, h, hvec, jump_target);
    }
  if (id_equal (name, "substitute"))
    {
      tree hvec = get_info_vec (loc, ctx, call, 1, non_constant_p,
				overflow_p, jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      return eval_substitute (loc, ctx, h, hvec, jump_target);
    }
  if (id_equal (name, "data_member_spec"))
    {
      tree opts = get_nth_callarg (call, 1);
      opts = cxx_eval_constant_expression (ctx, opts, vc_prvalue,
					   non_constant_p, overflow_p,
					   jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      return eval_data_member_spec (loc, ctx, h, opts, call,
				    non_constant_p, overflow_p, jump_target);
    }
  if (id_equal (name, "define_aggregate"))
    {
      tree hvec = get_info_vec (loc, ctx, call, 1, non_constant_p,
				overflow_p, jump_target);
      if (*jump_target)
	return NULL_TREE;
      if (*non_constant_p)
	return call;
      return eval_define_aggregate (loc, ctx, h, hvec, call, non_constant_p);
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
  reflect_kind kind;
  do
    {
      if (REFLECT_EXPR_KIND (lhs) != REFLECT_EXPR_KIND (rhs))
	return false;
      kind = static_cast <reflect_kind> (REFLECT_EXPR_KIND (lhs));
      lhs = REFLECT_EXPR_HANDLE (lhs);
      rhs = REFLECT_EXPR_HANDLE (rhs);
    }
  while (REFLECT_EXPR_P (lhs) && REFLECT_EXPR_P (rhs));

  lhs = resolve_nondeduced_context (lhs, tf_warning_or_error);
  rhs = resolve_nondeduced_context (rhs, tf_warning_or_error);

  /* TEMPLATE_DECLs are wrapped in an OVERLOAD.  When we have

       template_of (^^fun_tmpl<int>) == ^^fun_tmpl

     the RHS will be OVERLOAD<TEMPLATE_DECL> but the LHS will
     only be TEMPLATE_DECL.  They should compare equal, though.  */
  // ??? Can we do something better?
  lhs = OVL_FIRST (MAYBE_BASELINK_FUNCTIONS (lhs));
  rhs = OVL_FIRST (MAYBE_BASELINK_FUNCTIONS (rhs));
  if (kind == REFLECT_PARM)
    {
      lhs = maybe_update_function_parm (lhs);
      rhs = maybe_update_function_parm (rhs);
    }
  else if (kind == REFLECT_DATA_MEMBER_SPEC)
    return (TREE_VEC_ELT (lhs, 0) == TREE_VEC_ELT (rhs, 0)
	    && TREE_VEC_ELT (lhs, 1) == TREE_VEC_ELT (rhs, 1)
	    && tree_int_cst_equal (TREE_VEC_ELT (lhs, 2),
				   TREE_VEC_ELT (rhs, 2))
	    && tree_int_cst_equal (TREE_VEC_ELT (lhs, 3),
				   TREE_VEC_ELT (rhs, 3))
	    && TREE_VEC_ELT (lhs, 4) == TREE_VEC_ELT (rhs, 4));

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
