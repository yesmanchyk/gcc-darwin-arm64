// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

template <auto V> constexpr int e = [:V:];  // { dg-error ".int. is not usable in a splice expression" }
template <auto V> constexpr int e2 = [:V:]; // { dg-error ".int. is not usable in a splice expression" }
constexpr auto h = ^^int;
constexpr auto i = e<([:^^h:])>;
constexpr auto j = e2<^^int>;
