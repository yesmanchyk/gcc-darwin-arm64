// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test dependent splice specifiers.

#if 0
template<template<class> class X>
struct S {
  typename [: ^^X :]<int, float> m;
};

template<class> struct V1 {};
template<class, class = int> struct V2 {};

// S<V1> s1; // ILL-FORMED, type of S<V1>::m is invalid
S<V2> s2; // OK
#endif
