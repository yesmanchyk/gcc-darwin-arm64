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
 [: R :]<int> c0;
 [: T::r :]<int> c1;
 typename [: R :]<int> c2;
 typename [: T::r :]<int> c3;
}

void
f ()
{
  g<S, ^^Z>();
}
