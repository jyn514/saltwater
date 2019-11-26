// output: it is 2019


int sprintf(char *str, const char *format, ...);
        int puts(const char *s);
        int main() {
            char buf[100];
            sprintf(buf, "it is %d\n", 2019);
            puts(buf);
        }