// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

using info = decltype(^^void);

template<typename>
void foo () { }

template<info R>
void
fn ()
{
  // FIXME
  //int n = typename [:R:](42);
}

template void fn<^^foo<int>>();
