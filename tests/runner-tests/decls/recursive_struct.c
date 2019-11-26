// code: 1
struct p {
        int i;
        struct p *q;
    } my_p;
    int main() {
        my_p.q = &my_p;
        my_p.q->q->q->i = 1;
        return my_p.i;
    }
    