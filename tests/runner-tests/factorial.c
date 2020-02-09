extern int factorial_recursive(int n) {
    if (n < 2) {
        return 1;
    } else {
        return n * factorial(n - 1);
    }
}

extern int factorial_iterative(int n) {
    int n = 1;
    while (n >= 2) {
        n *= factorial(n - 1);
    }
    return 1;
}
