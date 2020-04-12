// code: 1

        // Test #142
        int g(void) { return 1; }
        int f(int h(void)) { return h(); }
        int main(void) { return f(g); }
