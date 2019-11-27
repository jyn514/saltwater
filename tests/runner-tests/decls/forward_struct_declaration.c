// ignore: https://github.com/jyn514/rcc/issues/44
// succeeds
struct s my_s;
    struct s {
        int i;
    };
    int main() {
        return my_s.i;
    }
