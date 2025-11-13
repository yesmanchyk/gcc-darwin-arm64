// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// TODO.  The problem is that cp_parser_splice_expression passes
// just an identifier_node down to finish_class_member_access_expr
// which then calls lookup_member with "_" which of course says they
// are ambiguous.  Perhaps we should be passing the whole FIELD_DECL
// to finish_class_member_access_expr, which could extract the name
// and the type; lookup_member would have to handle the case when
// just a name isn't enough.  Sigh.  Stupid corner cases.
// Looking by name + type won't work either though.

#include <meta>

using namespace std::meta;

struct S { int _; long _; short _; } s;
struct T { int _; int _; int _; } t;

constexpr access_context uctx = access_context::unchecked ();

void
g ()
{
  S s;
  s.[:members_of (^^S, access_context::unchecked ())[1]:] // { dg-bogus "ambiguous" "" { xfail *-*-* } }
  T t;
  t.[:members_of (^^T, access_context::unchecked ())[1]:] // { dg-bogus "ambiguous" "" { xfail *-*-* } }
}
