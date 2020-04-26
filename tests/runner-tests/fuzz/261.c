// compile-fail
// https://github.com/jyn514/rcc/issues/261
union u { int _; };
union u {
  union u {
    struct u _;
  } i: i;
};
