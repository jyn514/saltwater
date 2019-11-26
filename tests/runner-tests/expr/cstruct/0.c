// code: 2

struct s {
    int i, j, k;
} s;
int main() {
        int i = s.i = s.j = s.k = 1;
        struct s *sp = &s;
        sp->k = 2;
        return sp->k;
}