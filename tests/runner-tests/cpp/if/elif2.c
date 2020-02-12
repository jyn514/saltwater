// succeeds
// start -> if -> consume_all -> end
#if 1
int main() {}
#elif 1
syntax error 1
#elif 2
syntax error 2
#elif 0
syntax error 3
#elif 1
syntax error 4
#elif 0
syntax error 5
#else
syntax error 6
#endif
