// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

struct C {
  union {
    int i;
  };
};

struct D { int i; };

auto c = C{.i=2};
/* ??? Clang rejects this.  I don't know why; [expr.ref]/6 says
  "If E2 is a splice-expression, then let T1 be the type of E1.
  E2 shall designate either a member of T1 or a direct base class
  relationship (T1, B)."  But C::i is a member of C, as per
  [class.mem.general/3, yes?  */
auto v = c.[:^^C::i:];
// Clearly wrong.
auto e = c.[: ^^D::i :];  // { dg-error "not a base" }
