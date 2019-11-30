// succeeds
// https://github.com/jyn514/rcc/issues/123
int printf(char*, ...);
int f(int*);

int a[] = {1, 2, 3};
int main() {
    f(a);
}

int f(int *a) {
    return printf("%d\n", *(a+1));
}
