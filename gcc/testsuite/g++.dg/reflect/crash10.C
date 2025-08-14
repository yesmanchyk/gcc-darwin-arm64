// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

struct S { };
using X = S;

template <auto V> constexpr int e = [:V:];  // { dg-error ".X. is not usable in a splice expression" }
template <auto V> constexpr int e2 = [:V:]; // { dg-error ".X. is not usable in a splice expression" }
constexpr auto h = ^^X;
constexpr auto i = e<([:^^h:])>;
constexpr auto j = e2<^^X>;
