// compile-fail
// https://github.com/jyn514/rcc/issues/218
int main() {
    do {
        return 1;
    } while (1);
}
