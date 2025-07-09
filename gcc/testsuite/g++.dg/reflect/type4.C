// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test reflect-expression -> ^^ type-id.
// type-id:
//   type-specifier-seq abstract-declarator(opt)

enum E { E1 };
struct S { };
using T = int;
template<typename T>
class C {
  using type = T;
};
union U { int i; };

template<typename T>
using AT = C<T>;

void
f1 ()
{
  // type-specifier -> simple-type-specifier
  constexpr auto r1 = ^^void;
  constexpr auto r2 = ^^void*;
  constexpr auto r3 = ^^int&;
  constexpr auto r4 = ^^int&&;
  constexpr auto r5 = ^^decltype(sizeof(0));
  constexpr auto r6 = ^^E*;
  constexpr auto r7 = ^^S*;
  constexpr auto r8 = ^^T*;
  constexpr auto r9 = ^^const void*;
  constexpr auto r10 = ^^const int&;
  constexpr auto r11 = ^^E const*;
  constexpr auto r12 = ^^S const*const;
  constexpr auto r13 = ^^const T *;
  constexpr auto r14 = ^^E;
  constexpr auto r15 = ^^S;
  constexpr auto r16 = ^^T;
  constexpr auto r17 = ^^T&&;
  constexpr auto r18 = ^^int*[3];
  constexpr auto r19 = ^^int (*)[3];
  constexpr auto r20 = ^^int *();
  constexpr auto r21 = ^^int (*)(double);

  int i = 42;
  E e;
  S s;
  typename [: r1 :] fn1 ();
  typename [: r16 :] fn2 (typename [: r1 :]);
  [: r2 :] v1 = nullptr;
  [: r3 :] v2 = i;
  [: r4 :] v3 = 42;
  [: r5 :] v4 = 0U;
  [: r6 :] v5 = &e;
  [: r7 :] v6 = &s;
  [: r8 :] v7 = &i;
  [: r9 :] v8 = nullptr;
  [: r10 :] v9 = 42;
  [: r11 :] v10 = &e;
  [: r12 :] v11 = &s;
  [: r13 :] v12 = &i;
  [: r14 :] v13;
  [: r15 :] v14;
  [: r16 :] v15;
  [: r17 :] v16 = 42;
  [: r18 :] v17 = {nullptr};
  [: r19 :] v18;
  [: r20 :] v19;
  [: r21 :] v20;

  // type-specifier -> elaborated-type-specifier
  constexpr auto r22 = ^^struct S;
  constexpr auto r23 = ^^struct ::S;
  constexpr auto r24 = ^^struct C<int>;
  constexpr auto r25 = ^^struct ::C<int>;
  constexpr auto r26 = ^^struct ::template C<int>;
  constexpr auto r27 = ^^union U;
  constexpr auto r28 = ^^union ::U;
  constexpr auto r29 = ^^enum E;
  constexpr auto r30 = ^^enum ::E;
  constexpr auto r31 = ^^const struct S;
  constexpr auto r32 = ^^const struct ::S;
  constexpr auto r33 = ^^const struct C<int>;
  constexpr auto r34 = ^^const struct ::C<int>;
  constexpr auto r35 = ^^const struct ::template C<int>;
  constexpr auto r36 = ^^const union U;
  constexpr auto r37 = ^^const union ::U;
  constexpr auto r38 = ^^const enum E;
  constexpr auto r39 = ^^const enum ::E;

  [: r22 :] s1;
  [: r23 :] s2;
  [: r31 :] s3;
  [: r32 :] s4;
  [: r24 :] c1;
  [: r25 :] c2;
  [: r26 :] c3;
  [: r33 :] c4;
  [: r34 :] c5;
  [: r35 :] c6;
  [: r27 :] u1;
  [: r28 :] u2;
  [: r36 :] u3{1};
  [: r37 :] u4{1};
  [: r29 :] e1;
  [: r30 :] e2;
  [: r38 :] e3 = E1;
  [: r39 :] e4 = E1;

  // type-specifier -> typename-specifier
  constexpr auto r40 = ^^typename ::E;
  constexpr auto r41 = ^^typename ::C<int>;
  constexpr auto r42 = ^^typename ::template C<int>;
  constexpr auto r43 = ^^typename ::S;
  constexpr auto r44 = ^^typename ::T;
  constexpr auto r45 = ^^typename ::U;

  [: r40 :] e5;
  [: r41 :] c7;
  [: r42 :] c8;
  [: r43 :] s5;
  [: r44 :] i1;
  //[: r45 :] u5;

  constexpr auto r46 = ^^AT<int>;
  constexpr auto r47 = ^^::AT<int>;
  // FIXME PR119838
  //constexpr auto r48 = ^^::template AT<int>;
  constexpr auto r49 = ^^typename ::AT<int>;
  constexpr auto r50 = ^^typename ::template AT<int>;

  [: r46 :] c9;
  [: r47 :] c10;
  //[: r48 :] c11;
  [: r49 :] c12;
  [: r50 :] c13;
}
