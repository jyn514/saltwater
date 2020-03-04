#if 1
int main() {}
#if 0
syntax error
#endif
#elif 0
    #if 1
    syntax error 1
    #endif
    #if 0
    syntax error 2
    #elif 1
    syntax error 3
    #else
    syntax error 4
    #endif
syntax error 5
#elif 1
    #if 1
    syntax error 6
    #endif
syntax error 7
#endif
