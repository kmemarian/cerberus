#include "cerberus.h"
/* Generated by CIL v. 1.7.3 */
/* print_CIL_Input is false */

struct A {
   char a1[1] ;
   char a2[5] ;
   char a3[1] ;
   char a4[2041] ;
};
typedef unsigned long size_t;
struct A a  ;
extern void *memset(void * , int  , size_t  ) ;
extern void *memcpy(void * , void const   * , size_t  ) ;
extern int memcmp(void const   * , void const   * , size_t  ) ;
extern void abort(void) ;
void bar(struct A *x ) 
{ 
  size_t i ;
  int tmp ;

  {
  tmp = memcmp(x, "\001HELLO\001", sizeof("\001HELLO\001"));
  if (tmp) {
    abort();
  }
  i = 0;
  while (i < sizeof(x->a4)) {
    if (x->a4[i]) {
      abort();
    }
    i ++;
  }
  return;
}
}
int foo(void) 
{ 


  {
  memset(& a, 0, sizeof(a));
  a.a1[0] = 1;
  memcpy(a.a2, "HELLO", sizeof("HELLO"));
  a.a3[0] = 1;
  bar(& a);
  return (0);
}
}
int main(void) 
{ 


  {
  foo();
  return (0);
}
}
