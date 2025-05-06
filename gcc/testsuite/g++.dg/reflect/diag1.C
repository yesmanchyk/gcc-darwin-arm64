// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test that we offer some helpful diagnostic.

struct S {
  template<typename T>
  void tfn (T) { }
};

void
f ()
{
  S s;
  s.[: ^^S::tfn :](42); // { dg-error "reflection not usable in a template splice" }
// { dg-message "add .template. to denote a function template" "" { target *-*-* } .-1 }
  s.template [: ^^S::tfn :](42);
}
