# 1 "test1_unsat.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "test1_unsat.c"

void sassert(X) {}

void main()
{
    int x, y;
    int i;

    x = 6;

    for (i = 1; i < 100000; i++)
    {

        y++;
    }

    assert (x != 5);
}
