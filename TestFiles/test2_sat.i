# 1 "test2_sat.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "test2_sat.c"

void sassert(X) {}

int main()
{
    int i;
    int x, y;
    y = 7;
    x = 0;

    if (y == 7)
    {
        x = 5;
        for (i = 1; i < 100000; i++)
        {
            y++;
        }
        assert( x != 5);
    }

    return 0;
}
