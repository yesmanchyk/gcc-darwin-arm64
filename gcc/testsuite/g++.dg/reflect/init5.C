// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

using info = decltype(^^void);

struct Base { };
struct Derived : Base {
  info k;
  consteval Derived() : Base(), k(^^int) {}
};
consteval const Base &fn1() {
  static constexpr Derived d;
  return d;	      // { dg-error "conversion from consteval-only type" }
}
constexpr auto &ref = fn1();

consteval void *fn2() {
  static constexpr auto v = ^^int;
  return (void *)&v;  // { dg-error "conversion from consteval-only type" }
}
constexpr const void *ptr = fn2();
