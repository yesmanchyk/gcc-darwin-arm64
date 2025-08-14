// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

namespace N { }

template <auto V> constexpr int e = [:V:];  // { dg-error ".N. is not usable in a splice expression" }
template <auto V> constexpr int e2 = [:V:]; // { dg-error ".N. is not usable in a splice expression" }
constexpr auto h = ^^N;
constexpr auto i = e<([:^^h:])>;
constexpr auto j = e2<^^N>;
