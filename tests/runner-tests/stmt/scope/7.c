// code: 2
struct s {
    int i, j, k;
} s;
int main() {
        struct s *sp = &s;
        return sp->k = 2;
}
