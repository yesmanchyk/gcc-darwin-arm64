// TODO

#if 0
#include <meta>

using namespace std;
using namespace meta;
struct S {
    void foo(this S) {
    }
};
int main() {
    [:reflect_function(*&S::foo):](S());
}
#endif
