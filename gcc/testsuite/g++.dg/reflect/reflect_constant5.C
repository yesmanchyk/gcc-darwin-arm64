// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::reflect_constant.

#include <meta>

struct S {};
constexpr auto r = std::meta::reflect_constant (S{});
S s = [:r:];

struct R { int i; };
constexpr auto rr = std::meta::reflect_constant (R{42});
static_assert ([:rr:].i == 42);
