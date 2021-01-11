#include <assert.h>
#include <stdlib.h>
#include "sv.h"

void __assert_fail(const char *p1, const char *p2, unsigned int p3, const char *p4) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__))
{ 
  {
    assert(0);
  }
}

int __VERIFIER_nondet_int(void) 
{ 
  int __cil_tmp1 ;
  int __cil_tmp2 ;

  {
    __cil_tmp1 = rand();
    __cil_tmp2 = __cil_tmp1 % 11 - 5;
    return (__cil_tmp2);
  }
}

unsigned int __VERIFIER_nondet_uint(void) 
{ 
  unsigned int __cil_tmp1 ;
  unsigned int __cil_tmp2 ;

  {
    __cil_tmp1 = rand();
    __cil_tmp2 = __cil_tmp1 % 11;
    return (__cil_tmp2);
  }
}
