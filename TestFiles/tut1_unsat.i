# 1 "tut1_unsat.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "tut1_unsat.c"

void sassert(X) {}

int main()
{
 int x = 1;
 int y = 0;
 if (x > y)
 {
  x = y - x;
  assert(x > 0);
 }
 return 0;
}
