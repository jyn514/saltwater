// code: 1
struct s {
        int i;
        float f;
        union { int a; float b; } u;
    } m = { 1, 2.4, 3 };
    int main() { return m.i; }