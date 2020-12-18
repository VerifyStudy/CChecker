# 1 "test1_sat.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "test1_sat.c"

void sassert(X) {}

void main()
{
    int i;
    int x;
    int y;

    x = 6;

    for (i = 1; i < 100000; i++)
    {

        y++;
    }

    assert (x != 6);
}
