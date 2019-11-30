// output: BEGIN:
// *a: 1
// a[1]: 2
// *(a+1): 2
// *p: 1
// p[1]: 2
// *(p+1): 2
// END
int a[] = {1,2,3};
int printf(char*, ...);
int f(int*);
int main() {
    printf("*a: %d\n", *a);
    printf("a[1]: %d\n", a[1]);
    printf("*(a+1): %d\n", *(a+1));
    f(a);
}

int f(int *p) {
    printf("*p: %d\n", *p);
    printf("p[1]: %d\n", p[1]);
    printf("*(p+1): %d\n", *(p+1));
    return 0;
}
