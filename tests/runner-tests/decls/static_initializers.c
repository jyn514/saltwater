// code: 1
int i = 0,
        *p = &i,
        *q = 0,
        *r = (void*)0,
        f(void),
        (*fp)() = f,
        a[] = {1, 2, 3};
        struct s { int i; } my_s;
        int *s = &my_s.i;
    int f() { return 1; }
    int main() { return (*fp)(); }
