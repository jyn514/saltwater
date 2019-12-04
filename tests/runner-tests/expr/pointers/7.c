// code: 1
struct s {
        int i, j;
} my_s, *my_sp = &my_s;
int main() {
        return my_sp->j = 1;
}
