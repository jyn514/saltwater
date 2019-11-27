// ignore: https://github.com/jyn514/rcc/issues/95
// succeeds
int main() {
    int x = 0;
    if (0) goto fail;
    if (1) goto succeed;
    goto fail;

    succeed: return 0;
    fail: return 1;
}
