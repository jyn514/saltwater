// code: 1

        int g(void) { return 1; }
        int f(int h(void)) { return h(); }
        int main(void) { return f(g); }
