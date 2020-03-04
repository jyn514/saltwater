// code: 3
#if 1
int i = 1;
# else
#endif

# if 0
// check for nesting
# if 1
# if 1
#if 0
syntax error!!1!!1
// depth is at 4, pop them all off
#endif
more error!!#!131
#endif
fdsafdsa dsafda s
#endif
almost done
#endif

// oh yeah, expressions should work too
#if 1 + 2
int j = 2;
#endif

#if 0
error error
#elif 1
#define __restrict
#endif

int f(char *__restrict p, char *__restrict q) {
    return *p + *q;
}

int main() {
    return i + j;
}
