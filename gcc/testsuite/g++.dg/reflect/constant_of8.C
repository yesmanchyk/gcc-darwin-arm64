// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::constant_of, CWG 3111.

#include <meta>
using namespace std::meta;

constexpr int is[] = {1, 2, 3};
constexpr info r = reflect_constant_array (is);
static_assert (constant_of (^^is) == r);
