// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test comparison of reflections.

namespace N {
namespace foo {
struct foo {
  // FIXME See compare_reflections.
  //static_assert(^^foo == ^^::N::foo::foo);
};
static_assert(^^foo == ^^::N::foo::foo);
}

#if 0
namespace tfoo {
template <typename T> struct tfoo {
  static_assert(^^tfoo == ^^tfoo<T>);
};
static_assert(^^tfoo == ^^::N::tfoo::tfoo);

tfoo<int> instantiation;
}

static_assert(^^foo == ^^::N::foo);
static_assert(^^tfoo == ^^::N::tfoo);
#endif
}
