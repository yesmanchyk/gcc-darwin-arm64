// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::constant_of.

#include <meta>

using namespace std::meta;

[[=1, =1, =2, =1.0f]] void fn();
struct [[=3, =3, =4, =2.0f]] S;

template<info R>
[[=[:constant_of (annotations_of (R)[0]):]]] void bar();

template<info R>
struct [[=[:constant_of (annotations_of (R)[0]):]]] Y {};

// TODO Fix this ugly crash.
/* This ICEs because we get:
   <<< Unknown tree: splice_expr
  std::meta::constant_of (*std::meta::annotations_of (<<< Unknown tree: template_parm_index >>>).<<< Unknown tree: baselink >>> (0)) >>>
  which needs to be substituted before we can do anything about it.
  constant_of5.C has the same problem (with extract).  */

//constexpr auto y = constant_of (annotations_of (^^bar<^^::fn>)[0]);
//constexpr auto z = constant_of (annotations_of (^^Y<^^::S>)[0]);
