mod utils;
use utils::not_implemented;

#[test]
#[should_panic(expected = "not yet implemented: address loads")]
fn variable_expressions_not_implemented() {
    not_implemented("int x; int main() { return x; }");
}

#[test]
#[should_panic(expected = "expected statement")]
fn local_declarations_not_implemented() {
    not_implemented("int main() { int x; }");
}

#[test]
fn unary_plus() {
    utils::assert_code("int main() { return +1; }", 1);
    utils::assert_compile_error("int a[1]; int main() { return +a; }");
}

#[test]
fn negate() {
    utils::assert_code("int main() { return -(-4); }", 4);
    utils::assert_code("int main() { return -(-0); }", 0);
    utils::assert_code("int main() { return -(1) + 1; }", 0);
    utils::assert_compile_error("int a[1]; int main() { return -a; }");
}

#[test]
fn lnot() {
    utils::assert_code("int main() { return !1; }", 0);
    utils::assert_code("int main() { return !1.0; }", 0);
    utils::assert_code("int main() { return !0; }", 1);
    utils::assert_code("int main() { return !0.0; }", 1);
    utils::assert_code("int main() { return !(short)0; }", 1);
    utils::assert_code("int main() { return !(unsigned)0; }", 1);
    utils::assert_code("int main() { return !(_Bool)0; }", 1);
}

#[test]
fn bnot() {
    utils::assert_code("int main() { return ~-1; }", 0);
    utils::assert_code("int main() { return ~-2; }", 1);
    utils::assert_code("int main() { return ~0 + 1; }", 0);
    utils::assert_code("int main() { return ~1 + 2; }", 0);
    utils::assert_compile_error("int main() { return ~1.2; }");
    utils::assert_compile_error("int a[1]; int main() { return ~a; }");
}

#[test]
fn add() {
    utils::assert_succeeds("int main() { return 0 + 0; }");
    utils::assert_code("int main() { return 1 + 1; }", 2);
    utils::assert_code("int main() { return 1 + 2 + 3; }", 6);
    utils::assert_code("int main() { return 1.6 + 2.5; }", 4);
}

#[test]
fn sub() {
    utils::assert_code("int main() { return 0 - 0; }", 0);
    utils::assert_code("int main() { return 3 - 1; }", 2);
    utils::assert_code("int main() { return 10 - (1 - 2); }", 11);
    utils::assert_code("int main() { return 6.1 - 3.2; }", 2);
}

#[test]
fn mul() {
    utils::assert_code("int main() { return 1 * 10; }", 10);
    utils::assert_code("int main() { return 1 * 0; }", 0);
    utils::assert_code("int main() { return 3 * 4 * 5; }", 60);
    utils::assert_code("int main() { return 2.3 * 2.1; }", 4);
    utils::assert_compile_error("int a[1]; int main() { return a * 1; }");
}

#[test]
fn div() {
    utils::assert_code("int main() { return 10 / 2; }", 5);
    utils::assert_code("int main() { return 0 / 1; }", 0);
    utils::assert_code("int main() { return 4 / 3; }", 1);
    utils::assert_code("int main() { return 3.1 / 3.0; }", 1);
    utils::assert_compile_error("int a[1]; int main() { return a / 1; }");
}

#[test]
fn modulo() {
    utils::assert_code("int main() { return 6 % 3; }", 0);
    utils::assert_code("int main() { return 7 % 3; }", 1);
    utils::assert_code("int main() { return -7 % 3 + 1; }", 0);
    utils::assert_compile_error("int main() { return 1.0 % 2; }");
    utils::assert_compile_error("int a[1]; int main() { return a % 1; }");
}

#[test]
fn band() {
    utils::assert_code("int main() { return 1 & 1; }", 1);
    utils::assert_code("int main() { return 2 & 3; }", 2);
    utils::assert_code("int main() { return 0 & 10; }", 0);
    utils::assert_code("int main() { return -65 & 7; }", 7);
    utils::assert_compile_error("int main() { return 65 & 1.5; }");
    utils::assert_compile_error("int a[1]; int main() { return a & 1; }");
}

#[test]
fn bor() {
    utils::assert_code("int main() { return 1 | 2; }", 3);
    utils::assert_code("int main() { return 0 | 0; }", 0);
    utils::assert_code("int main() { return 105 | 0; }", 105);
    utils::assert_code("int main() { return (-1 | 0) + 1; }", 0);
    utils::assert_compile_error("int main() { return 1 | 1.5; }");
    utils::assert_compile_error("int a[1]; int main() { return a | 1; }");
}

#[test]
fn shift() {
    utils::assert_code("int main() { return 1 << 1; }", 2);
    utils::assert_code("int main() { return 2 << 3; }", 16);
    utils::assert_code("int main() { return 1 >> 1; }", 0);
    utils::assert_code("int main() { return 1 >> 10; }", 0);
    utils::assert_compile_error("int main() { return 1 >> 10.0; }");
    utils::assert_compile_error("int a[1]; int main() { return a >> 1; }");
    // should overflow and set sign bit
    //utils::assert_code("int main() { return (1 << 31) < 0; }", 1);
}

#[test]
fn xor() {
    utils::assert_code("int main() { return 0 ^ 0; }", 0);
    utils::assert_code("int main() { return 1 ^ 0; }", 1);
    utils::assert_code("int main() { return 5 ^ 2; }", 7);
    utils::assert_compile_error("int main() { return 5.2 ^ 1.2; }");
    utils::assert_compile_error("int a[1]; int main() { return a ^ 1; }");
}

#[test]
fn cmp() {
    utils::assert_code("int main() { return 1 == 1; }", 1);
    utils::assert_code("int main() { return 1 != 0; }", 1);
    utils::assert_code("int main() { return 1 > 0; }", 1);
    utils::assert_code("int main() { return 10 >= 0; }", 1);
    utils::assert_code("int main() { return 12 < 24; }", 1);
    utils::assert_code("int main() { return 12 <= 12; }", 1);
    utils::assert_code("int main() { return 12.0 <= 12.5; }", 1);
    utils::assert_code("int main() { return 12.0 != 12.1; }", 1);
    utils::assert_compile_error("int a[1]; int main() { return a == 1; }");
}

#[test]
fn comma() {
    utils::assert_code("int main() { return 1, 2; }", 2);
    utils::assert_code("int main() { return 1 + 1, 2.4; }", 2);
}

#[test]
fn implicit_casts() {
    utils::assert_code("int main() { return 1 + 1.0; }", 2);
    utils::assert_succeeds("int main() { return 1 - 1.0; }");
    utils::assert_code("int main() { return 1 * 1.0; }", 1);
    utils::assert_code("int main() { return 1 / 1.0; }", 1);
    utils::assert_code("int main() { return 1 == 1.0; }", 1);
    utils::assert_code("int main() { return 12.0 == 12; }", 1);
    utils::assert_code("int main() { return 12.0 <= 12; }", 1);
    utils::assert_code("int main() { return 1 + 2 > 1; }", 1);
}

#[test]
fn explicit_casts() {
    utils::assert_succeeds("int main() { return (short)0; }");
    utils::assert_succeeds("int main() { return (int)0.3; }");
    utils::assert_succeeds("int main() { return (_Bool)0.0; }");
    utils::assert_succeeds("int main() { return (float)0; }");
    utils::assert_succeeds("int main() { return (_Bool)(int*)(int)0.0; }");
}
