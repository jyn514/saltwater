// output: 1 2 3 4 5 6
int printf(const char *format, ...);

char h[][3] = {1, 2, 3};
int a[][3] = {{4,5,6}};

int main() {
    printf("%d %d %d %d %d %d\n",
            h[0][0], h[0][1], h[0][2],
            a[0][0], a[0][1], a[0][2]
          );
}
