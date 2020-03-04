// succeeds
int main() {
        int x;
        int *p;
        x = 0;
        p = &x;
        if(*p)
                return 1;
        return 0;
}
