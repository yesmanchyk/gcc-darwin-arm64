// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test from [dcl.type.splice].
// FIXME Missing the error.

struct S { using type = int; };
template <auto R> struct TCls {
  typename [:R:]::type member;  // typename applies to the qualified name
};

void fn() {
  //[:^^S::type:] *var;           // error: [:^^S::type:] is an expression
  typename [:^^S::type:] *var;  // OK, declares variable with type int*
}

using alias = [:^^S::type:];    // OK, type-only context
