// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::underlying_type.

#include <meta>

// Error, but don't crash.
//constexpr auto a = std::meta::underlying_type(^^int);
