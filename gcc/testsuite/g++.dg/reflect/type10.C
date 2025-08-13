// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

using info = decltype(^^void);

void fn1 ([: ^^int :]);
void fn2 ([: ^^int :] *);

constexpr auto r = ^^fn1;
void fn3 ([: r :]); // { dg-error "declared void" }

template<info R, info T>
void
g ()
{
  void foo([:R:]);
  foo (nullptr);

  int bar([:T:]);
  bar ({});
}

struct X { };

void
f ()
{
  g<^^int*, ^^X>();
}
