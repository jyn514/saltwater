// code: 1
typedef unsigned int __uid_t;
extern __uid_t getuid (void) ;

struct passwd {
  char *pw_name;
  char *pw_passwd;
};

extern struct passwd *getpwuid (__uid_t __uid);
extern int puts (const char *__s);

int main(void) {
  return puts(getpwuid(getuid())->pw_name) >= 0;
}
