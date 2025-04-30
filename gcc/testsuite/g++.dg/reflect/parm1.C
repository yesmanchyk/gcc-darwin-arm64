// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test reflections on types.

#include <meta>

// FIXME PR62244
//consteval int fn(decltype(^^::) x = ^^x) { return 0; }
//constexpr int x = fn ();

consteval auto
ref (std::meta::info r)
{
  return r;
}

consteval std::meta::info
def (std::meta::info r = std::meta::info(^^int))
{
  return r;
}

consteval std::meta::info
def2 (std::meta::info r = ^^int)
{
  return r;
}

void
g (int p)
{
  constexpr auto r = ref (^^int);
  [: r :] i1 = 42;
  typename [: r :] i2 = 42;
  [: ref (r) :] i3 = 42;

  constexpr auto r2 = def ();
  [: r2 :] i4 = 42;
  typename [: r2 :] i5 = 42;
  [: def () :] i6 = 42;

  constexpr auto r3 = def2 ();
  [: r3 :] i7 = 42;
  typename [: r3 :] i8 = 42;
  [: def2 () :] i9 = 42;

  constexpr auto r4 = std::meta::info(^^int);
  [: r4 :] i10 = 42;
  typename [: r4 :] i11 = 42;

  constexpr auto r5 = std::meta::info(r4);
  [: r5 :] i12 = 42;
  typename [: r5 :] i13 = 42;

  constexpr auto r6 = ^^p;
}
