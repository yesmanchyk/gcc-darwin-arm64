// { dg-do compile { target c++26 } }
// { dg-additional-options "-freflection" }
// Test reflections on types.

template<class, class> struct same_type;
template<class T> struct same_type<T, T> {};

const int && foo();
decltype(foo()) x1 = 17;       // type is const int&&
same_type<decltype(x1), const int &&> s1;
decltype([:^^x1:]) x5 = 18;    // type is const int&&
// FIXME need to set id_expression_or_member_access_p
//same_type<decltype(x5), const int &&> s2;
decltype(([:^^x1:])) x6 = 19;  // type is const int&
same_type<decltype(x6), const int &> s3;
