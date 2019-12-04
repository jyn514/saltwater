// fail
struct s;
int main() {
    // refers to a new struct, not the global struct s
    struct s { int i, j, k; } my_s;
}
int f() {
    struct s s2;
    return s2.i;
}
