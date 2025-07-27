// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test from [expr.const].

using info = decltype(^^int);

struct Base { };
struct Derived : Base { info r; };

consteval const Base& fn(const Derived& derived) { return derived; } // { dg-error "conversion from consteval-only type" }

constexpr Derived obj{.r=^^::}; // OK
constexpr const Derived& d = obj; // OK
constexpr const Base& b1 = fn(obj); // error: not a constant expression
  // because Derived is a consteval-only type but Base is not.
constexpr const Base& b2 = obj;	  // { dg-error "conversion from consteval-only type" }
constexpr Base b3 = obj;
