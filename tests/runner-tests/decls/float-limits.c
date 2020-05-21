// output: inf nan
int printf(const char *format, ...);

float INF = 1.0 / 0;
float NaN = 0.0 / 0;

int main() {
    // work around bugs in rustc: https://github.com/rust-lang/rust/issues/72411
    int NaN_positive_int = (*(int*)&NaN) & 0x7fffffff;
    float NaN_positive = *(float*)&NaN_positive_int;
    printf("%f %f\n", INF, NaN_positive);
}
