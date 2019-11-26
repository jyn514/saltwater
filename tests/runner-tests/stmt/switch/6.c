// succeeds
int a;
void print_one(), print_two(), print_three(), print_dunno();
int main() {
    switch(a) {
        case 1: print_one();
        case 2: print_two();
        case 3: print_three();
        default: print_dunno();
    }
}
void print_one() {}
void print_two() {}
void print_three() {}
void print_dunno() {}
