// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

#include <meta>

constexpr int i = 0;
// TODO Fix ICE
//const int p = ++std::meta::extract<const int &>(^^i);
