// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Cf. <https://github.com/cplusplus/CWG/issues/784>

class Base {
private:
  int m;
public:
  static constexpr auto rm = ^^m;
};
class Derived { static constexpr auto mp = &[:Base::rm:]; }; // { dg-bogus "is private within this context" "" { xfail *-*-* } }

class Base2 {
protected:
  int m;
public:
  static constexpr auto rm = ^^m;
};
class Derived2 { static constexpr auto mp = &[:Base2::rm:]; }; // { dg-bogus "is protected within this context" "" { xfail *-*-* } }
