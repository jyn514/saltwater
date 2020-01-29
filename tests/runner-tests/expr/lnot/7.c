// compile-fail
// https://github.com/jyn514/rcc/issues/212
void f();
int main() {
	switch(1) f(), !f();
}
