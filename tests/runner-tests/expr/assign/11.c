// succeeds
struct S {
    int x, y, z;
};

int main() {
    struct S s;
    struct S ss;
    s = ss;
}
