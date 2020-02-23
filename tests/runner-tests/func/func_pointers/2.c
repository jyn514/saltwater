// code: 1
int f(), (*fp)() = f;
    int main() {
            return fp();
    }
    int f() { return 1; }
