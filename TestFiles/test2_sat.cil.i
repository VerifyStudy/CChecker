# 1 "./test2_sat.cil.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "./test2_sat.cil.c"



void sassert(int X )
{


  {
  return;
}
}
extern int ( assert)() ;
int main(void)
{
  int i ;
  int x ;
  int y ;

  {
  y = 7;
  x = 0;
  if (y == 7) {
    x = 5;
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
  } else {

  }
  return (0);
}
}
