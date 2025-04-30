// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test reflections on types.

template<class, class> struct same_type;
template<class T> struct same_type<T, T> {};

using size_t = decltype(sizeof(int));
using info = decltype(^^void);
using T = int;

struct S { int i; };

constexpr auto g1 = ^^unsigned;
constexpr auto g2 = ^^S;
constexpr static auto g3 = ^^unsigned;
constexpr static auto g4 = ^^S;
constexpr info g5 = ^^void;
constexpr info g6 = ^^decltype(42);
constexpr info g7 = ^^T;
constexpr info g8 = ^^decltype(^^int);
constexpr info g9 = ^^void() const & noexcept;

[: g1 :] u1;
typename [: g1 :] u2;

namespace N {
  [: g1 :] nu1;
  typename [: g1 :] nu2;
}

void
f1 ()
{
  constexpr auto r1 = ^^int;
  [: r1 :] v1 = 42;
  typename [: r1 :] v1t = 42;
  same_type<decltype(v1), int>();
  same_type<decltype(v1t), int>();

  const [: r1 :] v2 = 42;
  same_type<decltype(v2), const int>();

  const volatile [: r1 :] v3 = 42;
  same_type<decltype(v3), const volatile int>();
  const [: r1 :] *v4 = &v1;
  same_type<decltype(v4), const int *>();

  constexpr auto r2 = ^^double;
  [: r2 :] v5 = 42.2;
  typename [: r2 :] v5t = 42.2;
  same_type<decltype(v5), double>();
  same_type<decltype(v5t), double>();

  [: r2 :] &v6 = v5;
  typename [: r2 :] &v6t = v5;
  same_type<decltype(v6), double &>();
  same_type<decltype(v6t), double &>();

  constexpr auto r3 = ^^S;
  [: r3 :] v7 = { 42 };
  typename [: r3 :] v7t = { 42 };
  same_type<decltype(v7), S>();
  same_type<decltype(v7t), S>();
  const [: r3 :] v8 = { 42 };
  same_type<decltype(v8), const S>();

  constexpr auto r4 = ^^long long int;
  [: r4 :] v9 = 0ll;
  typename [: r4 :] v9t = 0ll;
  same_type<decltype(v9), long long int>();
  same_type<decltype(v9t), long long int>();

  constexpr auto r5 = ^^const int;
  [: r5 :] v10 = 0;
  typename [: r5 :] v10t = 0;
  same_type<decltype(v10), const int>();
  same_type<decltype(v10t), const int>();

  constexpr auto r6 = ^^volatile short;
  [: r6 :] v11 = 0;
  typename [: r6 :] v11t = 0;
  same_type<decltype(v11), volatile short>();
  same_type<decltype(v11t), volatile short>();

  constexpr auto r7 = ^^bool;
  [: r7 :] v12 = 0;
  typename [: r7 :] v12t = 0;
  same_type<decltype(v12), bool>();
  same_type<decltype(v12t), bool>();

  constexpr auto r8 = ^^wchar_t;
  [: r8 :] v13 = 0;
  typename [: r8 :] v13t = 0;
  same_type<decltype(v13), wchar_t>();
  same_type<decltype(v13t), wchar_t>();

  constexpr auto r9 = ^^decltype(sizeof 0);
  [: r9 :] v14 = 0;
  typename [: r9 :] v14t = 0;
  same_type<decltype(v14), size_t>();
  same_type<decltype(v14t), size_t>();

  constexpr auto r10 = ^^signed;
  [: r10 :] v15 = 0;
  typename [: r10 :] v15t = 0;
  same_type<decltype(v15), int>();
  same_type<decltype(v15t), int>();

}

void
f2 ()
{
  [:^^char:] c1 = '*';
  same_type<decltype(c1), char>();

  const [:^^char:] c2 = '*';
  same_type<decltype(c2), const char>();

  [:^^int:]* c3 = nullptr;
  same_type<decltype(c3), int *>();

  [:^^int:] c4 = 42;
  same_type<decltype(c4), int>();

  [:^^int:] &c5 = c4;
  same_type<decltype(c5), int &>();

  [:^^int:] arr1[10];
  same_type<decltype(arr1), int[10]>();
}

// Like f2 but with typename.
void
f2t ()
{
  typename[:^^char:] c1 = '*';
  same_type<decltype(c1), char>();

  const typename[:^^char:] c2 = '*';
  same_type<decltype(c2), const char>();

  typename[:^^int:]* c3 = nullptr;
  same_type<decltype(c3), int *>();

  typename [:^^int:] c4 = 42;
  same_type<decltype(c4), int>();

  typename [:^^int:] &c5 = c4;
  same_type<decltype(c5), int &>();

  typename [:^^int:] arr1[10];
  same_type<decltype(arr1), int[10]>();
}

void
f3 ()
{
  [: g1 :] v1 = 42;
  same_type<decltype(v1), unsigned>();
  [: g3 :] v2 = 42;
  same_type<decltype(v2), unsigned>();
  [: g2 :] v3 = { 42 };
  same_type<decltype(v3), S>();
  [: g4 :] v4 = { 42 };
  same_type<decltype(v4), S>();
}

void
f3t ()
{
  typename [: g1 :] v1 = 42;
  same_type<decltype(v1), unsigned>();
  typename [: g3 :] v2 = 42;
  same_type<decltype(v2), unsigned>();
  typename [: g2 :] v3 = { 42 };
  same_type<decltype(v3), S>();
  typename [: g4 :] v4 = { 42 };
  same_type<decltype(v4), S>();
}

void
f4 ()
{
  static constexpr auto r = ^^unsigned;
  constexpr auto p = &r;
  [: *p :] i1 = 0u;
  typename [: *p :] i2 = 0u;
}

constexpr void
f5 ()
{
  static constexpr auto r = ^^unsigned;
  constexpr auto p = &r;
  [: *p :] i1 = 0u;
  typename [: *p :] i2 = 0u;
}

consteval void
f6 ()
{
  static constexpr auto r = ^^unsigned;
  constexpr auto p = &r;
  [: *p :] i1 = 0u;
  typename [: *p :] i2 = 0u;
  auto t = r;
  ^^int;
}

void
f7 ()
{
  {
    {
      constexpr auto r = ^^int;
      typename [: r :] v = 42;
      same_type<decltype(v), int>();
    }
  }
}

enum E { X, Y };
enum class SE { yay, nay };

void
f8 ()
{
  constexpr auto r = ^^E;
  [: r :] e = Y;
  typename [: r :] et;
  et = e;

  constexpr auto r2 = ^^SE;
  [: r2 :] e2 = SE::yay;
  typename [: r2 :] et2;
  et2 = e2;
}
