// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// TODO figure out how these should be mangled and then check it.
// For now, at least don't crash...

#include <meta>

template <std::meta::info I>
void foo ();

void
bar ()
{
  foo <^^::> ();
  foo <^^std::meta> ();
  foo <std::meta::info {}> ();
  foo <std::meta::reflect_constant (42)> ();
}
