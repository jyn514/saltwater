// compile-fail
int main() {
    switch(1)
      case 2: case 3: case 3:
        return 0;
}
