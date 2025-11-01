// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test std::meta::extract.

#include <meta>

using namespace std::meta;

void fn();
static_assert(annotations_of(^^fn).size() == 0);
[[=1, =2]] void fn();
static_assert(annotations_of(^^fn).size() == 2);
[[=3]] void fn();
static_assert(annotations_of(^^fn).size() == 3);
[[=4, =5]] void fn();
static_assert(annotations_of(^^fn).size() == 5);
[[=6]] void fn();
static_assert(annotations_of(^^fn).size() == 6);
void fn();
static_assert(annotations_of(^^fn).size() == 6);

constexpr auto idxOf = [](int v) consteval {
  auto annots = annotations_of(^^fn);
  for (size_t k = 0; k < annots.size(); ++k)
    if (extract<int>(annots[k]) == v)
      return k;

  __builtin_unreachable();
};
constexpr auto p1 = idxOf(1), p4 = idxOf(4);

static_assert(extract<int>(annotations_of(^^fn)[p1]) == 1);
static_assert(extract<int>(annotations_of(^^fn)[p1 + 1]) == 2);
static_assert(extract<int>(annotations_of(^^fn)[p1 + 2]) == 3);

static_assert(extract<int>(annotations_of(^^fn)[p4]) == 4);
static_assert(extract<int>(annotations_of(^^fn)[p4 + 1]) == 5);
static_assert(extract<int>(annotations_of(^^fn)[p4 + 2]) == 6);
