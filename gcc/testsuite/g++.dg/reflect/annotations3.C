// C++ 26 P3394R4 - Annotations for Reflection
// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::annotations_of.

#include <meta>

using namespace std::meta;

template<class, class> inline constexpr bool same_type_v = false;
template<class T> inline constexpr bool same_type_v<T, T> = true;

[[=42, =42]] int x;
static_assert (annotations_of (^^x).size () == 2);
static_assert (same_type_v<decltype (annotations_of (^^x)), std::vector<info>>);

[[=42]] int foo ();
[[=24]] int foo ();
static_assert (annotations_of (^^foo).size () == 2);

[[=1]] void bar ();
[[=2, =3]] void baz ();
void baz [[=4]] ();

static_assert (annotations_of (^^bar).size () == 1);
static_assert (annotations_of (^^baz).size () == 3);

struct [[=42]] C {};
constexpr std::meta::info a0 = annotations_of (^^C)[0];
static_assert (is_annotation (a0));

template <class T>
struct [[=42]] D {};

//constexpr std::meta::info a1 = annotations_of (^^D<int>)[0];
//constexpr std::meta::info a2 = annotations_of (^^D<char>)[0];
//static_assert (is_annotation (a1) && is_annotation (a2));

[[=1, =2L, =3.0, =4U, =5U, =6L, =7U]] int y;
static_assert (annotations_of (^^y).size () == 7);
static_assert (annotations_of_with_type (^^y, ^^int).size () == 1);
static_assert (annotations_of_with_type (^^y, ^^long).size () == 2);
static_assert (annotations_of_with_type (^^y, ^^unsigned).size () == 3);
static_assert (annotations_of_with_type (^^y, ^^const double).size () == 1);
static_assert (annotations_of_with_type (^^y, ^^volatile double).size () == 0);
static_assert (annotations_of_with_type (^^y, ^^float).size () == 0);

int z;
static_assert (annotations_of (^^z).size () == 0);
