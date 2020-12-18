# 1 "./ARMC_sat.cil.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "./ARMC_sat.cil.c"



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

  {
  x = 1;
  y = 0;
  {
  while (1) {
    while_continue: ;
    if (x <= 10) {

    } else {
      goto while_break;
    }
    x = x + 1;
    y = y + 1;
  }
  while_break: ;
  }
  {
  sassert(x == y);
  }
  return (0);
}
}
