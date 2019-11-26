// succeeds

    typedef unsigned char UC;
    union {
            UC UC[1];
    } data;
    int main () {
        return data.UC[0];
    }