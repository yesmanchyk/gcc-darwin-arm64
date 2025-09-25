// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }

// Copyright (C) 2025 Free Software Foundation, Inc.
//
// This file is part of the GNU ISO C++ Library.  This library is free
// software; you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the
// Free Software Foundation; either version 3, or (at your option)
// any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along
// with this library; see the file COPYING3.  If not see
// <http://www.gnu.org/licenses/>.

#include <type_traits>
#include <testsuite_tr1.h>

void test01()
{
  using std::is_consteval_only;
  using namespace __gnu_test;
  int v = 1;
  struct S1 { decltype(^^long) a; };
  union U2 { int a; decltype(^^test01) b; };
  struct S3 { const decltype(^^__gnu_test) *c; };
  struct S4 : public S3 {};
  struct S5 { int a; long *b; };

  static_assert(test_category<is_consteval_only, decltype(^^long)>(true), "");
  static_assert(test_category<is_consteval_only, const decltype(^^test01)>(true), "");
  static_assert(test_category<is_consteval_only, volatile decltype(^^__gnu_test)>(true), "");
  static_assert(test_category<is_consteval_only, const volatile decltype(^^v)>(true), "");
  static_assert(test_category<is_consteval_only, const S1>(true), "");
  static_assert(test_category<is_consteval_only, U2>(true), "");
  static_assert(test_category<is_consteval_only, S3>(true), "");
  static_assert(test_category<is_consteval_only, S4>(true), "");

  // Sanity check.
  static_assert(test_category<is_consteval_only, int>(false), "");
  static_assert(test_category<is_consteval_only, S5>(false), "");
}
