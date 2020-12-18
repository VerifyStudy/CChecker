# 1 "./Branch_sat.cil.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "./Branch_sat.cil.c"



void sassert(int X )
{


  {
  return;
}
}
int main(void)
{
  int b ;
  int a ;

  {
  b = 0;
  a = b - 1;
  {
  while (1) {
    while_continue: ;
    if (b < 8) {

    } else {
      goto while_break;
    }
    b = b + 1;
    if (b == 8) {
      a = 1;
    } else {

    }
  }
  while_break: ;
  }
  {
  sassert(a > 0);
  }
  return (0);
}
}
