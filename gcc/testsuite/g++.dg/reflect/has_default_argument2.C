// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::has_default_argument.

#include <meta>

void foo (int a, const int b = 42);
constexpr auto parminfo = std::meta::parameters_of (^^foo)[1];
void foo (int = 14, const int);
static_assert (std::meta::has_default_argument (parminfo));
static_assert (std::meta::type_of (parminfo) == ^^int);

void
foo (int c, const int d)
{
  constexpr auto p = std::meta::parameters_of (^^foo)[1];
  static_assert (p == parminfo);
  static_assert (std::meta::has_default_argument (p));
  static_assert (std::meta::type_of (p) == ^^int);
  static_assert (std::meta::type_of (std::meta::variable_of (p)) == ^^const int);
  static_assert (std::meta::type_of (^^d) == ^^const int);
  static_assert (std::meta::has_default_argument (parminfo));
  static_assert (std::meta::type_of (parminfo) == ^^int);
}
