// code: 1
enum e { A, B, C };
int f(enum e);
int main() {
    enum e my_e = B;
    return f(my_e);
}
int f(enum e e) {
    return e;
}