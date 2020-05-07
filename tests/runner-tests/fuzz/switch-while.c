// no-main
// https://github.com/jyn514/rcc/issues/404
void foo(void) {
  switch (1) {
    while(1) case 1:;
    case 0:;
  }
}
