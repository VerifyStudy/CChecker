# 1 "./test1_unsat.cil.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "./test1_unsat.cil.c"



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
  int i ;

  {
  x = 6;
  i = 1;
  {
  while (1) {
    while_continue: ;
    if (i < 100000) {

    } else {
      goto while_break;
    }
    y = y + 1;
    i = i + 1;
  }
  while_break: ;
  }
  {
  assert(x != 5);
  }
  return;
}
}
