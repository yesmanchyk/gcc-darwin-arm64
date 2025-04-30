// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::identifier_of.

#include <meta>

struct C { };

#if 0
constexpr std::string_view sv = std::meta::identifier_of(^^C);
static_assert(sv == "C");
static_assert(sv.data()[0] == 'C');
static_assert(sv.data()[1] == '\0');
#endif
