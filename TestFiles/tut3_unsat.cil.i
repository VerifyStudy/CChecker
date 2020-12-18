# 1 "./tut3_unsat.cil.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "./tut3_unsat.cil.c"



void sassert(int X )
{


  {
  return;
}
}
extern int ( assert)() ;
void main(void)
{
  int x ;
  int y ;
  int k ;

  {
  k = 3;
  x = 0;
  y = 0;
  {
  while (1) {
    while_continue: ;
    if (k > 0) {

    } else {
      goto while_break;
    }
    x = x + 1;
    y = y + 1;
    k = k - 1;
  }
  while_break: ;
  }
  {
  while (1) {
    while_continue___0: ;
    if (x > 0) {

    } else {
      goto while_break___0;
    }
    x = x - 1;
    y = y - 1;
  }
  while_break___0: ;
  }
  {
  assert(y == 0);
  }
  return;
}
}
