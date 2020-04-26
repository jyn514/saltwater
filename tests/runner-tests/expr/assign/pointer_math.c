// code: 0
// https://github.com/jyn514/rcc/issues/121
int main() {
    int i = 0, *p = &i;
    p += i;
    return i;
}
