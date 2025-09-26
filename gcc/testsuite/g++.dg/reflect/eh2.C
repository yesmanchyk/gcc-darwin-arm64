// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test throwing std::meta::exception.

#include <meta>

using namespace std::meta;

int i;
static_assert (is_reference_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_class_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_union_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_enum_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_member_function_pointer_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_member_object_pointer_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_pointer_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_array_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_void_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_null_pointer_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_integral_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_floating_point_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_lvalue_reference_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_rvalue_reference_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert (is_reflection_type (^^i)); // { dg-error "non-constant|uncaught exception" }
static_assert ((remove_const (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((remove_volatile (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((remove_cv (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((add_const (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((add_volatile (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((add_cv (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_object_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_arithmetic_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_member_pointer_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_scalar_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
