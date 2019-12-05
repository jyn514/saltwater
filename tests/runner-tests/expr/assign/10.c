// code: 5
struct S {
    int x;
};

int main() {
    struct S s;
    struct S ss;
    return (s = ss).x = 5;
}
