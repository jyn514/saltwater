// code: 2

#define a
#define b

#if defined(a)
int i = 2;
#endif

#ifndef b
syntax error
#endif

# if defined b && defined(a)
    int main() { return i; }
#endif
