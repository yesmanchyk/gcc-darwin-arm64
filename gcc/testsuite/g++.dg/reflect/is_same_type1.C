// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::is_same_type.

#include <meta>

using namespace std::meta;

using U = int;
using UU = U;

static_assert (is_same_type (^^int, ^^int));
static_assert (is_same_type (^^int, ^^U));
static_assert (is_same_type (^^int, ^^UU));
static_assert (!is_same_type (^^int, ^^const int));
static_assert (!is_same_type (^^int, ^^const UU));
static_assert (!is_same_type (^^int *, ^^int[]));
static_assert (!is_same_type (^^int&, ^^int&&));
