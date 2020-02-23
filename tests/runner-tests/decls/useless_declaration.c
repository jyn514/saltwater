// succeeds
struct s {
            struct inner {
                int i;
            };
            int j;
        };
        struct inner my_inner;
        int main() {
            return my_inner.i;
        }
