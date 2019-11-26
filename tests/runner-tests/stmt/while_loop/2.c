// succeeds

int f(void) {
    int i;
    while (0) {
        if (1)
            i = 1;
        else
            return 1;
    }
    return 0;
}
int main() { return f(); }