// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// https://github.com/cplusplus/CWG/issues/705
// This should probably be rejected.

auto f() {
  union { int what; };
  return &[:^^what:];  // { dg-warning "address of local variable" }
}
