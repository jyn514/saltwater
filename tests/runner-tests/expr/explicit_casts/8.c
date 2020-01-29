// compile-fail
// https://github.com/jyn514/rcc/issues/212
void f();
int main() {
    return (int)f();
}
