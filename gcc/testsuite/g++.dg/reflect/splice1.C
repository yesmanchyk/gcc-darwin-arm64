// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

#include <meta>
#include <ranges>

using namespace std::meta;

struct S {
  int mem;
  int : 5;
};
struct T : public S {
};

[[=1]] void
foo ()
{
  S s = { 0 }, t = { 0 };
  constexpr auto ctx = access_context::unchecked ();
  s.[: members_of (^^S, ctx)[1] :] = 1;	// { dg-error "cannot use an unnamed bit-field in a splice expression" }
  s.[: (members_of (^^S, ctx) | std::views::filter (is_default_constructor) | std::ranges::to <std::vector> ())[0] :] ();	// { dg-error "cannot call constructor 'S::S' directly" }
  s.[: (members_of (^^S, ctx) | std::views::filter (is_copy_constructor) | std::ranges::to <std::vector> ())[0] :] (t);		// { dg-error "cannot call constructor 'S::S' directly" }
  // TODO, this should be diagnosed too.  And perhaps the above 2 differently.
  s.[: (members_of (^^S, ctx) | std::views::filter (is_destructor) | std::ranges::to <std::vector> ())[0] :] ();		// { dg-error "" "" { xfail *-*-* } }
  // TODO: The two below ICE.
  // [: annotations_of (^^foo)[0] :];
  // [: data_member_spec (^^S, { .name = "name" }) :];
  [: bases_of (^^T, ctx)[0] :];													// { dg-error "" "" { xfail *-*-* } }
}
