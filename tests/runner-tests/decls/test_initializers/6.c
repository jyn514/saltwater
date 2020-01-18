// ignore: https://github.com/lifthrasiir/hexf/issues/6
// output: index.html
int puts(const char *s);

static const char *index_page = "index.html";

int main() {
    puts(index_page);
}
