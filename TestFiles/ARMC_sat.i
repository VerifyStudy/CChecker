# 1 "ARMC_sat.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "ARMC_sat.c"

void sassert(X){}

int main()
{
    int x = 1;
    int y = 0;
    while(x <= 10)
    {
        x = x + 1;
        y = y + 1;
    }
    sassert(x == y);
    return 0;
}
