// code: 2
#define f g(a)
#define g(b) c
int main() {
    int a = 1, c = 2;
    return f;
}
