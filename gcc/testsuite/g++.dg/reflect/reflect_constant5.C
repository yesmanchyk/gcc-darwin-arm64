// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::reflect_constant.

#include <meta>

struct S {};
constexpr auto r = std::meta::reflect_constant (S{});
S s = [:r:];
static_assert (!is_value (r));
static_assert (is_object (r));

struct R { int i; };
constexpr auto rr = std::meta::reflect_constant (R{42});
static_assert ([:rr:].i == 42);
static_assert (!is_value (rr));
static_assert (is_object (rr));
