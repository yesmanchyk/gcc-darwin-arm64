// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::reflect_constant.  The glvalue-to-prvalue conversion may have
// side-effects as part of the constant expression evaluation that the call to
// reflect_constant is part of.

#include <meta>

using namespace std::meta;

struct A {
  int *const p;
  consteval A(int *p) : p(p) {}
  consteval A(const A &oth) : p(nullptr) {
    if (oth.p) {
      ++*oth.p;
    }
  }
};

consteval int f() {
  int x = 42;
  A a(&x);
  reflect_constant (a);
  return x;
}

// ??? Clang++ accepts this, but we throw: we think that the temporary
// argument to reflect_constant can't be a NTTP.
static_assert(f() == 43); // { dg-error "uncaught exception|non-constant" }
