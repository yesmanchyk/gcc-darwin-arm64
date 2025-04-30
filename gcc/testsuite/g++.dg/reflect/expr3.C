// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

int x = 42;
template<typename T>
constexpr T two = 2;

template<typename T>
constexpr T foo (T t) { return t; }

void
g ()
{
  int i1 = [: ^^x :];
  int i2 = template [: ^^x :];    // { dg-error "reflection not usable in a template splice" }
  int i3 = [: ^^two<int> :];
  int i4 = template [: ^^two<int> :]; // { dg-error "reflection not usable in a template splice" }
  int i5 = [: ^^foo :](42);	      // { dg-error "reflection not usable in a template splice" }
  int i6 = template [: ^^foo :](42);
  int i7 = [: ^^foo<int> :](42);
  int i8 = template [: ^^foo<int> :](42);   // { dg-error "reflection not usable in a template splice" }
  int i9 = [: ^^foo :]<int>(42);	    // { dg-error "reflection not usable in a template splice" }
  int i10 = template [: ^^foo :]<int>(42);
}
