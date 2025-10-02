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
static_assert ((is_fundamental_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_compound_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((remove_reference (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((add_lvalue_reference (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((add_rvalue_reference (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((make_signed (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((make_unsigned (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((remove_extent (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((remove_all_extents (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((remove_pointer (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((add_pointer (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_const_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_volatile_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_trivially_copyable_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_trivially_relocatable_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_replaceable_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_standard_layout_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_empty_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_polymorphic_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_abstract_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_final_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_aggregate_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_consteval_only_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_signed_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_unsigned_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_bounded_array_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_unbounded_array_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
static_assert ((is_scoped_enum_type (^^i), true)); // { dg-error "non-constant|uncaught exception" }
