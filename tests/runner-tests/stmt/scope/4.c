// code: 1
int main() {
        struct T { int x; } s1;
        {
                struct T { int y; } s2;
                s1.x = 1;
        }
        return s1.x;
}
