// output: BEGIN: abcdefghij END
int putchar(char);
int main() {
        for (int i = 0; i < 10; i += 1) {
                putchar('a' + i);
        }
}
