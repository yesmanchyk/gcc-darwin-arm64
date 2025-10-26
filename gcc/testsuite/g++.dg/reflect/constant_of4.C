// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::constant_of.

#include <meta>

using namespace std::meta;

struct S {
  int k;
  int bf:32;
};

constexpr info null_reflection;
static union { int m; };
namespace NS { }
using T = int;

consteval bool
constant_of_ok (info r)
{
  try { constant_of (r); }
  catch (std::meta::exception &) { return false; }
  return true;
}

static_assert (!constant_of_ok (^^S::k));
static_assert (!constant_of_ok (^^m));
static_assert (!constant_of_ok (^^int));
static_assert (!constant_of_ok (^^NS));
static_assert (!constant_of_ok (^^S::bf));
static_assert (!constant_of_ok (null_reflection));
static_assert (!constant_of_ok (^^T));

template<typename>
struct X { };
// I suppose the [:^^X:] splice-expression is valid, so we don't throw.
constexpr auto v = constant_of (^^X); // { dg-error "" }
static_assert (!constant_of_ok (^^X<int>));

constexpr int foo () { return 42; }
constexpr auto v2 = constant_of (^^foo); // { dg-error "" }

template<int N>
constexpr int bar () { return N; }
constexpr auto v3 = constant_of (^^bar); // { dg-error "" }

template<int N>
constexpr int V = N;

static_assert (!constant_of_ok (^^V));

int x = 10;
static_assert (!constant_of_ok (^^x));
