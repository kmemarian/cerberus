#include "cerberus.h"
/* Generated by CIL v. 1.7.3 */
/* print_CIL_Input is false */

struct __anonstruct_t_1 {
   void *super ;
   int name ;
   int size ;
};
typedef struct __anonstruct_t_1 t;
extern int ( /* missing proto */  malloc)() ;
extern int ( /* missing proto */  memcpy)() ;
t *f(t *clas , int size ) 
{ 
  t *child ;
  int tmp ;

  {
  tmp = malloc(size);
  child = (t *)tmp;
  memcpy(child, clas, clas->size);
  child->super = clas;
  child->name = 0;
  child->size = size;
  return (child);
}
}
extern int ( /* missing proto */  memset)() ;
extern int ( /* missing proto */  abort)() ;
extern int ( /* missing proto */  exit)() ;
int main(void) 
{ 
  t foo ;
  t *bar ;

  {
  memset(& foo, 37, sizeof(t ));
  foo.size = sizeof(t );
  bar = f(& foo, sizeof(t ));
  if (((unsigned long )bar->super != (unsigned long )(& foo) || bar->name != 0) || (unsigned long )bar->size != sizeof(t )) {
    abort();
  }
  exit(0);
}
}
