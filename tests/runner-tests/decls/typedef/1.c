// code: 1
typedef int DWORD, INT, *INT_POINTER;
    INT main() {
        DWORD i = 1;
        INT_POINTER p = &i;
        return *p;
    }
