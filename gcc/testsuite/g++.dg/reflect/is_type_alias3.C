// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::is_type_alias.

#include <meta>

using namespace std::meta;

typedef int I;
static_assert (is_type_alias (^^I));
static_assert (!is_type_alias (^^const I));
static_assert (!is_type_alias (^^I const));
static_assert (!is_type_alias (^^I &&));
static_assert (^^I != ^^int);
static_assert (^^const I == ^^const int);
static_assert (^^I const == ^^const int);
// TODO, shall these be equal?
//static_assert (^^I && == ^^int &&);

typedef const int J;
static_assert (is_type_alias (^^J));
static_assert (!is_type_alias (^^const J));
static_assert (!is_type_alias (^^J const));
static_assert (!is_type_alias (^^J &));
static_assert (^^J != ^^const int);
static_assert (^^const J == ^^const int);
static_assert (^^J const == ^^const int);
// TODO, shall these be equal?
//static_assert (^^J & == ^^const int &);
