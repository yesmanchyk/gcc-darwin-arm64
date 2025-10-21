// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// List of Types to List of Sizes

#include <algorithm>
#include <array>
#include <meta>
#include <ranges>

constexpr std::array types = {^^int, ^^float, ^^double};
constexpr std::array sizes = []{
  std::array<std::size_t, types.size()> r;
  std::ranges::transform(types, r.begin(), std::meta::size_of);
  return r;
}();
