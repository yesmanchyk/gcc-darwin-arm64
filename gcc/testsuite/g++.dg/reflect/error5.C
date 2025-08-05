// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

using info = decltype(^^void);

namespace N { }

template<info R>
void
f ()
{
  int i = [:R:]; // { dg-error "void value not ignored as it ought to be" }
}

void
g ()
{
  f<^^N>();
}
