// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

using info = decltype(^^void);

template<typename T>
constexpr T magic = 1234;

template<info R>
void
f ()
{
  [:R:] r;	// { dg-error "not usable in a splice type" }
  [:R:]<int> r; // { dg-error "conflicting declaration" }
}

void
g ()
{
  f<^^magic>();
}
