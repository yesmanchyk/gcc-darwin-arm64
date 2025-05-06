// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test using enum.

enum class Color { R, G, B };
struct S { using enum Color; };

static_assert(^^S::R != ^^S::G);
static_assert(^^S::R != ^^Color::R);
//static_assert(dealias(^^S::R) == ^^Color::R);
//static_assert(is_entity_proxy(^^S::R));
static_assert([:^^S::R:] == Color::R);
