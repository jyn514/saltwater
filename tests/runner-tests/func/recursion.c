// code: 8

    int fib(unsigned n) {
        if (n < 2) return 1;
        return fib(n - 2) + fib(n - 1);
    }
    int main(void) { return fib(5); }
