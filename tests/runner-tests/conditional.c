// output: 2 1
#include <stdio.h>
int main(void) {
    int i = 0, j = 1;
    i = j == 1 ? 1, 2 : 3;
    printf("%d %d\n", i, j);
}
