// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

using info = decltype(^^int);

consteval int
foo (info i)
{
  return 42;
}

consteval info
bar ()
{
  return ({ constexpr auto a = ^^int; a; });
}

struct S {
  info i;
};

void
g ()
{
  constexpr int i = foo (({ constexpr auto a = ^^int; a; }));
  static constexpr info r = ({ constexpr auto a = ^^int; a; });
  constexpr info o = bar ();
  constexpr auto sz = sizeof (({ constexpr auto a = ^^int; a; }));
  constexpr S s{({ constexpr auto a = ^^int; a; })};
}
