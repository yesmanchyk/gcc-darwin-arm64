// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// From clang/test/Reflection/splice-exprs.cpp.

using info = decltype(^^int);

struct S {
  int j;
  int k;

  consteval int getJ() const { return j; }

  template <int N>
  consteval int getJPlusN() const { return j + N; }

  static consteval int eleven() { return 11; }

  template <int N>
  static consteval int constant() { return N; }
};

// Splicing dependent member references.
template <info RMem>
consteval int fn() {
  S s = {11, 13};
  return s.[:RMem:] + (&s)->[:RMem:];
}
static_assert(fn<^^S::j>() == 22);
static_assert(fn<^^S::k>() == 26);

// Splicing dependent member references with arrow syntax.
template <info RMem>
consteval int fn2() {
  S s = {11, 13};
  return s.*(&[:RMem:]) + (&s)->*(&[:RMem:]);
}
static_assert(fn<^^S::j>() == 22);
static_assert(fn<^^S::k>() == 26);

// Splicing member functions.
constexpr info r_getJ = ^^S::getJ;
static_assert(S{2, 4}.[:r_getJ:]() == 2);

// Splicing static member functions.
constexpr auto rEleven = ^^S::eleven;
static_assert([:rEleven:]() == 11);

// Splicing static member template function instantiation.
constexpr auto rConst14 = ^^S::constant<14>;
static_assert([:rConst14:]() == 14);
