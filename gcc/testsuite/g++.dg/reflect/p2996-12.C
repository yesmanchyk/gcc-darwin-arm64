// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test from [basic.splice].

using info = decltype(^^int);

constexpr int v = 1;
template<int V> struct TCls {
  static constexpr int s = V + 1;
};

// OK, a splice-specialization-specifier with a splice-expression as a template argument
using alias = [:^^TCls:]<([:^^v:])>;

static_assert(alias::s == 2);

// FIXME -- should be an error.
auto o1 = [:^^TCls:]<([:^^v:])>();
// OK, o2 is an object of type TCls<1>
auto o2 = typename [:^^TCls:]<([:^^v:])>();

consteval int bad_splice(info v) {
  return [:v:];	  // { dg-error ".v. is not a constant expression" }
}
