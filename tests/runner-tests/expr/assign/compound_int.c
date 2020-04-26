// errors: 5
// https://github.com/jyn514/rcc/issues/214
int main () {
    float f = 1;
    f %= 2;
    f ^= 3;
    f &= 4;
    f <<= 5;
    f >>= 5;
}
