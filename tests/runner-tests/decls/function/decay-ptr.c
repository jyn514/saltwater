// code: 2

int f(int g()) { return g(); }
int h(void) { return 2; }
int main(void) {
        return f(h);
}
