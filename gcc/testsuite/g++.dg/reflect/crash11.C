// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

template<typename T>
struct Z {};

struct S {
  static constexpr auto r = ^^Z;
};

template<typename T, auto R>
void
g ()
{
  template [: R :]<int> c0; // { dg-error "not usable in a splice expression|expected" }
  template [: T::r :]<int> c1;  // { dg-error "not usable in a splice expression|expected" }
}

void
f ()
{
  g<S, ^^Z>();
}
