// success
// start -> consume_if -> elif -> consume_all -> end
#if 0
syntax error 1
#elif 0
syntax error 2
#elif 0
syntax error 3
#elif 1
int main() {}
#elif 0
syntax error 4
#else
syntax error 5
#endif
