// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test throwing std::meta::exception.

#include <meta>

using namespace std::meta;

consteval void
eval (int n)
{
  switch (n)
    {
    case 0:
      is_reference_type (^^n);
      break;
    case 1:
      is_class_type (^^n);
      break;
    case 2:
      is_union_type (^^n);
      break;
    case 3:
      is_enum_type (^^n);
      break;
    case 4:
      is_member_function_pointer_type (^^n);
      break;
    case 5:
      is_member_object_pointer_type (^^n);
      break;
    case 6:
      is_array_type (^^n);
      break;
    case 7:
      is_pointer_type (^^n);
      break;
    case 8:
      is_void_type (^^n);
      break;
    case 9:
      is_null_pointer_type (^^n);
      break;
    case 10:
      is_integral_type (^^n);
      break;
    case 11:
      is_floating_point_type (^^n);
      break;
    case 12:
      is_lvalue_reference_type (^^n);
      break;
    case 13:
      is_rvalue_reference_type (^^n);
      break;
    case 14:
      is_reflection_type (^^n);
      break;
    case 15:
      remove_const (^^n);
      break;
    case 16:
      remove_volatile (^^n);
      break;
    case 17:
      remove_cv (^^n);
      break;
    case 18:
      add_const (^^n);
      break;
    case 19:
      add_volatile (^^n);
      break;
    case 20:
      add_cv (^^n);
      break;
    default:
      break;
    }
}

consteval bool
test (int n)
{
  try { eval (n); }
  catch (std::meta::exception &) { return true; }
  catch (...) { return false; }
  return false;
}

static_assert (test (0));
static_assert (test (1));
static_assert (test (2));
static_assert (test (3));
static_assert (test (4));
static_assert (test (5));
static_assert (test (6));
static_assert (test (7));
static_assert (test (8));
static_assert (test (9));
static_assert (test (10));
static_assert (test (11));
static_assert (test (12));
static_assert (test (13));
static_assert (test (14));
static_assert (test (15));
static_assert (test (16));
static_assert (test (17));
static_assert (test (18));
static_assert (test (19));
static_assert (test (20));
