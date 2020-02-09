// output: BEGIN:
// hi
// hello
// hi
// END
int puts(const char*);
int *s1 = "hi", *s2 = "hello", *s3 = "hi";

int main() {
	puts(s1);
	puts(s2);
	puts(s3);
}
