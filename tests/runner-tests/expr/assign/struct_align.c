// code: 1
int main() {
	struct S { int *y, z; } s, ss;
	ss.z = 1;
	s = ss;
	return s.z;
}
