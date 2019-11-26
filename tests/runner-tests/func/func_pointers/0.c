// code: 1

int (*func)();
int f() { return 1; }
int main() {
    func = &f;
    return (*func)();
}