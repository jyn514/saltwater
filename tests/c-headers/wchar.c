typedef float _Float32;
typedef double _Float64;
typedef double _Float32x;
typedef long double _Float64x;
typedef long unsigned int size_t;
typedef int wchar_t;
typedef __builtin_va_list __gnuc_va_list;
typedef unsigned int wint_t;
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
struct _IO_FILE;
typedef struct _IO_FILE __FILE;
struct _IO_FILE;
typedef struct _IO_FILE FILE;
struct __locale_struct
{
  struct __locale_data *__locales[13];
  const unsigned short int *__ctype_b;
  const int *__ctype_tolower;
  const int *__ctype_toupper;
  const char *__names[13];
};
typedef struct __locale_struct *__locale_t;
typedef __locale_t locale_t;

struct tm;
extern wchar_t *wcscpy (wchar_t * __dest,
   const wchar_t * __src)
     ;
extern wchar_t *wcsncpy (wchar_t * __dest,
    const wchar_t * __src, size_t __n)
     ;
extern wchar_t *wcscat (wchar_t * __dest,
   const wchar_t * __src)
     ;
extern wchar_t *wcsncat (wchar_t * __dest,
    const wchar_t * __src, size_t __n)
     ;
extern int wcscmp (const wchar_t *__s1, const wchar_t *__s2)
     ;
extern int wcsncmp (const wchar_t *__s1, const wchar_t *__s2, size_t __n)
     ;
extern int wcscasecmp (const wchar_t *__s1, const wchar_t *__s2) ;
extern int wcsncasecmp (const wchar_t *__s1, const wchar_t *__s2,
   size_t __n) ;
extern int wcscasecmp_l (const wchar_t *__s1, const wchar_t *__s2,
    locale_t __loc) ;
extern int wcsncasecmp_l (const wchar_t *__s1, const wchar_t *__s2,
     size_t __n, locale_t __loc) ;
extern int wcscoll (const wchar_t *__s1, const wchar_t *__s2) ;
extern size_t wcsxfrm (wchar_t * __s1,
         const wchar_t * __s2, size_t __n) ;
extern int wcscoll_l (const wchar_t *__s1, const wchar_t *__s2,
        locale_t __loc) ;
extern size_t wcsxfrm_l (wchar_t *__s1, const wchar_t *__s2,
    size_t __n, locale_t __loc) ;
extern wchar_t *wcsdup (const wchar_t *__s) ;
extern wchar_t *wcschr (const wchar_t *__wcs, wchar_t __wc)
     ;
extern wchar_t *wcsrchr (const wchar_t *__wcs, wchar_t __wc)
     ;
extern size_t wcscspn (const wchar_t *__wcs, const wchar_t *__reject)
     ;
extern size_t wcsspn (const wchar_t *__wcs, const wchar_t *__accept)
     ;
extern wchar_t *wcspbrk (const wchar_t *__wcs, const wchar_t *__accept)
     ;
extern wchar_t *wcsstr (const wchar_t *__haystack, const wchar_t *__needle)
     ;
extern wchar_t *wcstok (wchar_t * __s,
   const wchar_t * __delim,
   wchar_t ** __ptr) ;
extern size_t wcslen (const wchar_t *__s) ;
extern size_t wcsnlen (const wchar_t *__s, size_t __maxlen)
     ;
extern wchar_t *wmemchr (const wchar_t *__s, wchar_t __c, size_t __n)
     ;
extern int wmemcmp (const wchar_t *__s1, const wchar_t *__s2, size_t __n)
     ;
extern wchar_t *wmemcpy (wchar_t * __s1,
    const wchar_t * __s2, size_t __n) ;
extern wchar_t *wmemmove (wchar_t *__s1, const wchar_t *__s2, size_t __n)
     ;
extern wchar_t *wmemset (wchar_t *__s, wchar_t __c, size_t __n) ;
extern wint_t btowc (int __c) ;
extern int wctob (wint_t __c) ;
extern int mbsinit (const mbstate_t *__ps) ;
extern size_t mbrtowc (wchar_t * __pwc,
         const char * __s, size_t __n,
         mbstate_t * __p) ;
extern size_t wcrtomb (char * __s, wchar_t __wc,
         mbstate_t * __ps) ;
extern size_t __mbrlen (const char * __s, size_t __n,
   mbstate_t * __ps) ;
extern size_t mbrlen (const char * __s, size_t __n,
        mbstate_t * __ps) ;
extern size_t mbsrtowcs (wchar_t * __dst,
    const char ** __src, size_t __len,
    mbstate_t * __ps) ;
extern size_t wcsrtombs (char * __dst,
    const wchar_t ** __src, size_t __len,
    mbstate_t * __ps) ;
extern size_t mbsnrtowcs (wchar_t * __dst,
     const char ** __src, size_t __nmc,
     size_t __len, mbstate_t * __ps) ;
extern size_t wcsnrtombs (char * __dst,
     const wchar_t ** __src,
     size_t __nwc, size_t __len,
     mbstate_t * __ps) ;
extern double wcstod (const wchar_t * __nptr,
        wchar_t ** __endptr) ;
extern float wcstof (const wchar_t * __nptr,
       wchar_t ** __endptr) ;
extern long double wcstold (const wchar_t * __nptr,
       wchar_t ** __endptr) ;
extern long int wcstol (const wchar_t * __nptr,
   wchar_t ** __endptr, int __base) ;
extern unsigned long int wcstoul (const wchar_t * __nptr,
      wchar_t ** __endptr, int __base)
     ;

extern long long int wcstoll (const wchar_t * __nptr,
         wchar_t ** __endptr, int __base)
     ;

extern unsigned long long int wcstoull (const wchar_t * __nptr,
     wchar_t ** __endptr,
     int __base) ;
extern wchar_t *wcpcpy (wchar_t * __dest,
   const wchar_t * __src) ;
extern wchar_t *wcpncpy (wchar_t * __dest,
    const wchar_t * __src, size_t __n)
     ;
extern __FILE *open_wmemstream (wchar_t **__bufloc, size_t *__sizeloc) ;
extern int fwide (__FILE *__fp, int __mode) ;
extern int fwprintf (__FILE * __stream,
       const wchar_t * __format, ...)
                                                           ;
extern int wprintf (const wchar_t * __format, ...)
                                                           ;
extern int swprintf (wchar_t * __s, size_t __n,
       const wchar_t * __format, ...)
     ;
extern int vfwprintf (__FILE * __s,
        const wchar_t * __format,
        __gnuc_va_list __arg)
                                                           ;
extern int vwprintf (const wchar_t * __format,
       __gnuc_va_list __arg)
                                                           ;
extern int vswprintf (wchar_t * __s, size_t __n,
        const wchar_t * __format,
        __gnuc_va_list __arg)
     ;
extern int fwscanf (__FILE * __stream,
      const wchar_t * __format, ...)
                                                          ;
extern int wscanf (const wchar_t * __format, ...)
                                                          ;
extern int swscanf (const wchar_t * __s,
      const wchar_t * __format, ...)
     ;
extern int __isoc99_fwscanf (__FILE * __stream,
        const wchar_t * __format, ...);
extern int __isoc99_wscanf (const wchar_t * __format, ...);
extern int __isoc99_swscanf (const wchar_t * __s,
        const wchar_t * __format, ...)
     ;
extern int vfwscanf (__FILE * __s,
       const wchar_t * __format,
       __gnuc_va_list __arg)
                                                          ;
extern int vwscanf (const wchar_t * __format,
      __gnuc_va_list __arg)
                                                          ;
extern int vswscanf (const wchar_t * __s,
       const wchar_t * __format,
       __gnuc_va_list __arg)
     ;
extern int __isoc99_vfwscanf (__FILE * __s,
         const wchar_t * __format,
         __gnuc_va_list __arg);
extern int __isoc99_vwscanf (const wchar_t * __format,
        __gnuc_va_list __arg);
extern int __isoc99_vswscanf (const wchar_t * __s,
         const wchar_t * __format,
         __gnuc_va_list __arg) ;
extern wint_t fgetwc (__FILE *__stream);
extern wint_t getwc (__FILE *__stream);
extern wint_t getwchar (void);
extern wint_t fputwc (wchar_t __wc, __FILE *__stream);
extern wint_t putwc (wchar_t __wc, __FILE *__stream);
extern wint_t putwchar (wchar_t __wc);
extern wchar_t *fgetws (wchar_t * __ws, int __n,
   __FILE * __stream);
extern int fputws (const wchar_t * __ws,
     __FILE * __stream);
extern wint_t ungetwc (wint_t __wc, __FILE *__stream);
extern size_t wcsftime (wchar_t * __s, size_t __maxsize,
   const wchar_t * __format,
   const struct tm * __tp) ;

