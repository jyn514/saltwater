// no-main
extern int factorial_recursive(int n) {
    if (n < 2) {
        return 1;
    } else {
        return n * factorial_recursive(n - 1);
    }
}

extern int factorial_iterative(int n) {
    int sum = 1;
    while (n >= 2) {
        sum *= n--;
    }
    return 1;
}
