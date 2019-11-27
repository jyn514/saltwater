// output: 6
int putchar(int);
int main() {
    unsigned char a = 255, b = 1;
    int sum = a + b;
    putchar('0' + sum%10);
    putchar('\n');
}
