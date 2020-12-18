# 1 "./Loop_sat.cil.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "./Loop_sat.cil.c"



void sassert(int X )
{


  {
  return;
}
}
int main(void)
{
  int x ;
  int y ;
  int z ;

  {
  x = 1;
  y = 2;
  z = 0;
  {
  while (1) {
    while_continue: ;
    if (x < y) {

    } else {
      goto while_break;
    }
    x = x + 1;
  }
  while_break: ;
  }
  {
  sassert(x >= z);
  }
  return (0);
}
}
