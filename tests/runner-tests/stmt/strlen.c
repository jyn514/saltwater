// ignore
// this is https://github.com/jyn514/rcc/issues/92
// code: 2

    typedef unsigned long size_t;
    size_t strlen(char *str) {
        size_t len = 0;
        while (*str++) ++len;
        return len;
    }
    int main() { return strlen("hi"); }
