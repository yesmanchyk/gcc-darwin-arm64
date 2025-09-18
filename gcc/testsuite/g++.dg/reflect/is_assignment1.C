// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::is_assignment.

#include <meta>

using namespace std::meta;

constexpr info null_reflection;
void foo ();

struct S {
  S &operator = (const S &);
  S &operator += (const S &);
  void bar ();
};

struct T {
  T &operator = (const S &);
  T &operator *= (const S &);
};

struct U {
  U &operator = (U &&);
};

static_assert (!is_assignment (^^null_reflection));
static_assert (!is_assignment (^^int));
static_assert (!is_assignment (^^::));
static_assert (!is_assignment (^^foo));
static_assert (!is_assignment (^^S::bar));
static_assert (is_assignment (^^S::operator =));
static_assert (!is_assignment (^^S::operator +=));
static_assert (!is_assignment (^^T::operator *=));
// T::operator = and U::operator = are overloads and
// so we need probably members_of to test those.
