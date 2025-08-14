// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

using info = decltype(^^void);

namespace N { }

template<info R>
void
f ()
{
  int i = [:R:]; // { dg-error ".N. is not usable in a splice expression" }
}

void
g ()
{
  f<^^N>();
}
