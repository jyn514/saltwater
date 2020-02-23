// fail

int main() {
    int f();
    return f();
}

int g() {
    return f();
}
