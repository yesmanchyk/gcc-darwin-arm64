// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test reflection type traits [meta.reflection.traits], type properties.

#include <meta>
using namespace std::meta;

struct A { A (A &&) = default; A &operator= (A &&) = default; ~A () = default; int a; };

static_assert (is_trivially_relocatable_type (^^A));
static_assert (is_nothrow_relocatable_type (^^A));
static_assert (is_replaceable_type (^^A));

struct B { B (B &&); B &operator= (B &&) = default; ~B () = default; int a; };

static_assert (!is_trivially_relocatable_type (^^B));
static_assert (!is_nothrow_relocatable_type (^^B));
static_assert (!is_replaceable_type (^^B));

struct C { C (C &&) = default; C &operator= (C &&); ~C () = default; int a; };

static_assert (!is_trivially_relocatable_type (^^C));
static_assert (is_nothrow_relocatable_type (^^C));
static_assert (!is_replaceable_type (^^C));

struct D { D (D &&) = delete; D &operator= (D &&) = default; int a; };

static_assert (!is_trivially_relocatable_type (^^D));
static_assert (!is_nothrow_relocatable_type (^^D));
static_assert (!is_replaceable_type (^^D));

struct E { E (E &&) = default; E &operator= (E &&) = delete; int a; };

static_assert (!is_trivially_relocatable_type (^^E));
static_assert (is_nothrow_relocatable_type (^^E));
static_assert (!is_replaceable_type (^^E));

struct F { F (F &&) = default; F &operator= (F &&) = default; ~F () = delete; int a; };

static_assert (!is_trivially_relocatable_type (^^F));
static_assert (!is_nothrow_relocatable_type (^^F));
static_assert (!is_replaceable_type (^^F));

struct G { G (const G &) = default; G &operator= (const G &) = default; int a; };

static_assert (is_trivially_relocatable_type (^^G));
static_assert (is_nothrow_relocatable_type (^^G));
static_assert (is_replaceable_type (^^G));

struct H { H (const H &); H &operator= (const H &) = default; int a; };

static_assert (!is_trivially_relocatable_type (^^H));
static_assert (!is_nothrow_relocatable_type (^^H));
static_assert (!is_replaceable_type (^^H));

struct I { I (const I &) = default; I &operator= (const I &); ~I () = default; int a; };

static_assert (!is_trivially_relocatable_type (^^I));
static_assert (is_nothrow_relocatable_type (^^I));
static_assert (!is_replaceable_type (^^I));

struct J { J (const J &) = delete; J &operator= (const J &) = default; int a; };

static_assert (!is_trivially_relocatable_type (^^J));
static_assert (!is_nothrow_relocatable_type (^^J));
static_assert (!is_replaceable_type (^^J));

struct K { K (const K &) = default; K &operator= (const K &) = delete; int a; };

static_assert (!is_trivially_relocatable_type (^^K));
static_assert (is_nothrow_relocatable_type (^^K));
static_assert (!is_replaceable_type (^^K));

struct M;
struct L { L (L &&) = default; L (M &&); L &operator= (L &&) = default; int a; };

static_assert (is_trivially_relocatable_type (^^L));
static_assert (is_nothrow_relocatable_type (^^L));
static_assert (is_replaceable_type (^^L));

struct M : public L { using L::L; M (const M &); M &operator= (M &&) = default; int b; };

static_assert (!is_trivially_relocatable_type (^^M));
static_assert (!is_nothrow_relocatable_type (^^M));
static_assert (!is_replaceable_type (^^M));

struct O;
struct N { N (N &&) = default; N &operator= (N &&) = default; N &operator= (O &&); int a; };

static_assert (is_trivially_relocatable_type (^^N));
static_assert (is_nothrow_relocatable_type (^^N));
static_assert (is_replaceable_type (^^N));

struct O : public N { using N::operator=; O (O &&) = default; int b; };

static_assert (!is_trivially_relocatable_type (^^O));
static_assert (is_nothrow_relocatable_type (^^O));
static_assert (!is_replaceable_type (^^O));

struct Q;
struct P { template <typename T> P (T &&) {} };

static_assert (is_trivially_relocatable_type (^^P));
static_assert (is_nothrow_relocatable_type (^^P));
static_assert (is_replaceable_type (^^P));

struct Q : public P { using P::P; Q (const Q &); };

static_assert (!is_trivially_relocatable_type (^^Q));
static_assert (!is_nothrow_relocatable_type (^^Q));
static_assert (!is_replaceable_type (^^Q));

struct S;
struct R { R (const R &) = default; R (const M &); R &operator= (R &&) = default; int a; };

static_assert (is_trivially_relocatable_type (^^R));
static_assert (is_nothrow_relocatable_type (^^R));
static_assert (is_replaceable_type (^^R));

struct S : public R { using R::R; S &operator= (S &&) = default; int b; };

static_assert (!is_trivially_relocatable_type (^^S));
static_assert (!is_nothrow_relocatable_type (^^S));
static_assert (!is_replaceable_type (^^S));

struct T { T (T &&) = default; T &operator= (T &&) = default; ~T (); int a; };

static_assert (!is_trivially_relocatable_type (^^T));
static_assert (is_nothrow_relocatable_type (^^T));
static_assert (!is_replaceable_type (^^T));

struct U { U (const U &) = default; U &operator= (const U &) = default; ~U (); int a; };

static_assert (!is_trivially_relocatable_type (^^U));
static_assert (is_nothrow_relocatable_type (^^U));
static_assert (!is_replaceable_type (^^U));

struct V { public: V (); private: V (V &&) = default; V &operator= (V &&) = default; ~V () = default; int a; };

static_assert (is_trivially_relocatable_type (^^V));
static_assert (is_nothrow_relocatable_type (^^V));
static_assert (is_replaceable_type (^^V));
