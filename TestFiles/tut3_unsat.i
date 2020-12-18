# 1 "tut3_unsat.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "tut3_unsat.c"

void sassert(X) {}

void main()
{
 int x, y;
 int k = 3;
 x = 0;
 y = 0;
 while (k > 0)
 {
  x++;
  y++;
  k--;
 }
 while (x > 0)
 {
  x--;
  y--;
 }
 assert(y == 0);
 return 0;
}
