// compile-fail
struct s {
    struct int i;
} S;
struct t {} T;

int main() {
    &S + 0;
    &T + 0;
}
