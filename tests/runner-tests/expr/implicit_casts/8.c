// code: 1
int main() {
        int i = 1, *p = &i;
        char *c = p;
        void *d = p;
        p = d;
        c = d;
        return *c;
        }