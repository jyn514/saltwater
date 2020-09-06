#ifndef __STDC_STDARG_H
#define __STDC_STDARG_H

// va_list is a built-in type
// TODO: this gives awful error messages because I don't show the macros it was expanded from
// In the meantime, make the error message all one token so it will show up in the parse error.
#define va_arg(ap, type) (va_arg not_currently_supported_by_saltwater)
#define va_copy(dst, src) (va_copy not_currently_supported_by_saltwater)
#define va_end(ap) (va_end not_currently_supported_by_saltwater)
#define va_start(ap, named_param) (va_start not_currently_supported_by_saltwater)

typedef __builtin_va_list va_list;
// glibc is awful and I hate it
typedef __builtin_va_list __gnuc_va_list;

#endif
