// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Otherwise, if the id-expression denotes a local entity E for which
// there is a lambda scope that intervenes between R and the point at
// which E was introduced, R is ill-formed.

static int s1;

void
f ()
{
  int l1;
  static int s2;
  constexpr auto rl1 = ^^l1;
  [] -> decltype(^^s1,
		 ^^l1,	  // { dg-error "intervening lambda expression" "" { xfail *-*-* } }
		 s2) {
    int l2;

    constexpr auto rl1_2 = ^^l1;  // { dg-error "intervening lambda expression" }
    constexpr auto rl2 = ^^l2;

    return s1;
  };
}

void
g ()
{
  int x;
  [=]<auto r> {
    static_assert(^^x == r);  // { dg-error "intervening lambda expression" }
  }.operator()<^^x>();
}
