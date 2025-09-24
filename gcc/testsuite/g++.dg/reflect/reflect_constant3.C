// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::reflect_constant.

#include <meta>

using namespace std::meta;

static_assert ([:reflect_constant (42):] == 42);
//static_assert (type_of (reflect_constant (42)) == ^^int);

enum E { A = 42 };
static_assert ([:reflect_constant (A):] == A);
//static_assert (type_of (reflect_constant (E::A)) == ^^E);

enum class EC { A = 42 };
static_assert ([:reflect_constant (EC::A):] == EC::A);
//static_assert (type_of (reflect_constant (EC::A)) == ^^EC);

const int i = 42;
static_assert ([:reflect_constant (i):] == i);
//static_assert (type_of (reflect_constant (i)) == ^^int);

const int &r = 42;
static_assert ([:reflect_constant (r):] == r);
//static_assert (type_of (reflect_constant (r)) == ^^int);

constexpr int ci = 42;
static_assert ([:reflect_constant (ci):] == ci);
//static_assert (type_of (reflect_constant (ci)) == ^^int);

void fn() {}
static_assert ([:reflect_constant (&fn):] == &fn);
//static_assert (type_of (reflect_constant (&fn)) == ^^void(*)());

constexpr int cfn () { return 42; }
static_assert ([:reflect_constant (cfn ()):] == 42);
//static_assert (type_of (reflect_constant (cfn ())) == ^^int);

struct S {
  int k;
  void fn();
};
static_assert ([:reflect_constant (&S::k):] == &S::k);
//static_assert (type_of (reflect_constant (&S::k)) == ^^int (S::*));
static_assert ([:reflect_constant (&S::fn):] == &S::fn);
//static_assert (type_of (reflect_constant (&S::fn)) == ^^void (S::*)());
