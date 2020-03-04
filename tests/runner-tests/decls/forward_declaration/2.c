// succeeds

    typedef struct s *sp;
    struct s { int i; } my_s;
    int main() {
        sp my_p = &my_s;
        return my_p->i = 0;
    }
