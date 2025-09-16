// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test throwing std::meta::exception.

#include <meta>

using namespace std::meta;

struct S { };

consteval void
eval (int n)
{
  switch (n)
    {
    case 0:
      is_same_type (^^S, ^^n);
      break;
    case 1:
      is_same_type (^^n, ^^S);
      break;
    case 2:
      is_base_of_type (^^S, ^^n);
      break;
    case 3:
      is_base_of_type (^^n, ^^S);
      break;
    case 4:
      is_virtual_base_of_type (^^S, ^^n);
      break;
    case 5:
      is_virtual_base_of_type (^^n, ^^S);
      break;
    case 6:
      is_convertible_type (^^S, ^^n);
      break;
    case 7:
      is_convertible_type (^^n, ^^S);
      break;
    case 8:
      is_nothrow_convertible_type (^^S, ^^n);
      break;
    case 9:
      is_nothrow_convertible_type (^^n, ^^S);
      break;
    case 10:
      is_layout_compatible_type (^^S, ^^n);
      break;
    case 11:
      is_layout_compatible_type (^^n, ^^S);
      break;
    case 12:
      is_pointer_interconvertible_base_of_type (^^S, ^^n);
      break;
    case 13:
      is_pointer_interconvertible_base_of_type (^^n, ^^S);
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
