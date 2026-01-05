#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "target.h"
#include "tm.h"
#include "cp-tree.h"
#include "stringpool.h" // for get_identifier
#include "intl.h"
#include "attribs.h"
// #include "c-family/c-pragma.h" // for parse_in
// #include "gimplify.h" // for unshare_expr

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

  // vector_identifier = get_identifier ("vector");

  // TREE_TYPE (std_meta_node) = void_type_node;
}

tree
get_reflection (location_t loc, tree t)
{
  t = build1_loc (loc, REFLECT_EXPR, meta_info_type_node, t);
  TREE_CONSTANT (t) = true;
  TREE_READONLY (t) = true;
  TREE_SIDE_EFFECTS (t) = false;
  return t;
}

