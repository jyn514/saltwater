// output: j is 6
#include<stdio.h>

typedef struct s *sp;

int i = 1;
int a[3] = {1, 2, 3};
float f = 2.5;

struct s {
  int outer;
} my_struct;

int g(int);

int main(void) {
  sp my_struct_pointer = &my_struct;
  const int c = my_struct_pointer->outer = 4;
  // should return 6
  int j = i + f*a[2] - c/g(1);
  printf("j is %d\n", j);
  return j;
}

int g(int i) {
  if (i < 0 || i >= 3) {
    return 0;
  }
  return a[i];
}
