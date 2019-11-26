// output: fedcba

    int putchar(int);
    int main() {
        int i = 5;
        while (i >= 0) {
                putchar(i + 'a');
                i -= 1;
        }
    }