// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::has_identifier.

#include <meta>

constexpr std::meta::info null_reflection;

struct S { };
using T = int;
using U = S;

static_assert (!std::meta::has_identifier (null_reflection));
static_assert (!std::meta::has_identifier (^^int));
static_assert (!std::meta::has_identifier (^^T));
static_assert (!std::meta::has_identifier (^^::));
static_assert (std::meta::has_identifier (^^S));
static_assert (std::meta::has_identifier (^^U));

void
g ()
{
  __extension__ constexpr bool b = std::meta::has_identifier (({ struct S2 { }; ^^S2; }));
}
