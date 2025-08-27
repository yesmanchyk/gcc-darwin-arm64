// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test reflection type traits [meta.reflection.traits].

#include <meta>
using namespace std::meta;

struct cls {
  using type = int;
  void mem_fun ();
  static void static_mem_fun ();
};
struct empty { };
using alias = cls;
struct derived : cls { };
union onion {
  onion &operator=(const cls&);
  onion &operator=(cls&&);
};
enum class Enum : short {};
enum class Enum_class { A };
class abstract_cls { virtual void fn() = 0; };
class final_cls final {};
struct ctor_cls {
  ctor_cls (int, bool) noexcept {}
};
struct trivial_cls {
  int i;
  bool b;
};
class virtual_dtor_cls {
  virtual ~virtual_dtor_cls () {}
};
int fun (bool, char) noexcept { return 0; }

static_assert (!is_function_type (^^void));
static_assert (!is_function_type (^^int));
static_assert (!is_function_type (^^const int));
static_assert (!is_function_type (^^volatile int));
static_assert (!is_function_type (^^unsigned));
static_assert (!is_function_type (^^float));
static_assert (!is_function_type (^^int&));
static_assert (!is_function_type (^^int&&));
static_assert (!is_function_type (^^int *));
static_assert (!is_function_type (^^int[1]));
static_assert (!is_function_type (^^int[]));
static_assert (!is_function_type (^^nullptr_t));
static_assert (!is_function_type (^^std::meta::info));
static_assert (!is_function_type (^^int (cls::*)));
static_assert (!is_function_type (^^int (cls::*)()));
static_assert (!is_function_type (^^cls));
static_assert (!is_function_type (^^empty));
static_assert (!is_function_type (^^abstract_cls));
static_assert (!is_function_type (^^final_cls));
static_assert (!is_function_type (^^ctor_cls));
static_assert (!is_function_type (^^trivial_cls));
static_assert (!is_function_type (^^virtual_dtor_cls));
static_assert (!is_function_type (^^onion));
static_assert (!is_function_type (^^Enum));
static_assert (!is_function_type (^^Enum_class));
static_assert (is_function_type (^^void ()));

static_assert (is_void_type (^^void));
static_assert (is_void_type (^^const void));
static_assert (is_void_type (^^volatile void));
static_assert (!is_void_type (^^void *));
static_assert (!is_void_type (^^int));
static_assert (!is_void_type (^^const int));
static_assert (!is_void_type (^^volatile int));
static_assert (!is_void_type (^^unsigned));
static_assert (!is_void_type (^^float));
static_assert (!is_void_type (^^int&));
static_assert (!is_void_type (^^int&&));
static_assert (!is_void_type (^^int *));
static_assert (!is_void_type (^^int[1]));
static_assert (!is_void_type (^^int[]));
static_assert (!is_void_type (^^nullptr_t));
static_assert (!is_void_type (^^std::meta::info));
static_assert (!is_void_type (^^int (cls::*)));
static_assert (!is_void_type (^^int (cls::*)()));
static_assert (!is_void_type (^^cls));
static_assert (!is_void_type (^^empty));
static_assert (!is_void_type (^^abstract_cls));
static_assert (!is_void_type (^^final_cls));
static_assert (!is_void_type (^^ctor_cls));
static_assert (!is_void_type (^^trivial_cls));
static_assert (!is_void_type (^^virtual_dtor_cls));
static_assert (!is_void_type (^^onion));
static_assert (!is_void_type (^^Enum));
static_assert (!is_void_type (^^Enum_class));
static_assert (!is_void_type (^^void ()));
