// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

static union { int m; };
constexpr auto r = ^^m;
auto p = [:r:]; // { dg-error "cannot implicitly reference a class member through a splice" }

namespace N {
  static union { int mn; };
  constexpr auto rn = ^^mn;
  auto pn = [:rn:];  // { dg-error "cannot implicitly reference a class member through a splice" }
}

struct S {
  union {
    int m;
  };
};

constexpr auto p2 = [: ^^S::m :]; // { dg-error "cannot implicitly reference a class member through a splice" }

void
f ()
{
  static union {
    int x;
  };
  auto rx = [: ^^x :]; // { dg-error "cannot implicitly reference a class member through a splice" }

  union {
    union {
      int u;
    };
  };
  auto ru = [: ^^u :]; // { dg-error "cannot implicitly reference a class member through a splice" }

  struct L {
    union {
      int z;
    };
  };
  auto rz = [: ^^L::z :]; // { dg-error "cannot implicitly reference a class member through a splice" }
}
