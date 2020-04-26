// compile-fail
// https://github.com/jyn514/rcc/issues/244

struct S {
    int x, y, z;
};

int main() {
    struct S s;
    struct S ss;
    s &= ss;
}
