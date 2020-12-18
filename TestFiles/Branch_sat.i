# 1 "Branch_sat.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "Branch_sat.c"

void sassert(X) {}

int main()
{
 int b = 0;
 int a = b - 1;
 while (b < 8)
 {
  b = b + 1;
  if (b == 8)
  {
   a = 1;
  }
  else
  {
  }
 }
 sassert(a > 0);
 return 0;
}
