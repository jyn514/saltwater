// code: 2
int i = 0, *p = &i, f(), (*fp)() = f, a[] = {1, 2, 3};
struct s {
    int i;
    float f;
    union { int a; float b; } u;
} m = { 1, 2.4, { 3 } };

int main() {
    return m.f;
}

int f() { return 0; }
