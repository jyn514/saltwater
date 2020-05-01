// no-main
// https://github.com/jyn514/rcc/issues/2
int f(int *restrict p, int *restrict q) {
    return *p + *q;
}
