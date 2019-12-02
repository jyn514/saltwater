
typedef int __jmp_buf[6];
typedef struct
{
  unsigned long int __val[(1024 / (8 * sizeof (unsigned long int)))];
} __sigset_t;
struct __jmp_buf_tag
  {
    __jmp_buf __jmpbuf;
    int __mask_was_saved;
    __sigset_t __saved_mask;
  };
typedef struct __jmp_buf_tag jmp_buf[1];
extern int setjmp (jmp_buf __env) ;
extern int __sigsetjmp (struct __jmp_buf_tag __env[1], int __savemask) ;
extern int _setjmp (struct __jmp_buf_tag __env[1]) ;
extern void longjmp (struct __jmp_buf_tag __env[1], int __val)
     ;
extern void _longjmp (struct __jmp_buf_tag __env[1], int __val)
     ;
typedef struct __jmp_buf_tag sigjmp_buf[1];
extern void siglongjmp (sigjmp_buf __env, int __val)
     ;

