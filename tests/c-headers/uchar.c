typedef long unsigned int size_t;
typedef struct
{
  int __count;
  union
  {
    unsigned int __wch;
    char __wchb[4];
  } __value;
} __mbstate_t;
typedef __mbstate_t mbstate_t;

extern size_t mbrtoc16 (char16_t * __pc16,
   const char * __s, size_t __n,
   mbstate_t * __p) ;
extern size_t c16rtomb (char * __s, char16_t __c16,
   mbstate_t * __ps) ;
extern size_t mbrtoc32 (char32_t * __pc32,
   const char * __s, size_t __n,
   mbstate_t * __p) ;
extern size_t c32rtomb (char * __s, char32_t __c32,
   mbstate_t * __ps) ;

