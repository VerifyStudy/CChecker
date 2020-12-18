# 1 "Loop_sat.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "Loop_sat.c"

void sassert(X){}

int main()
{
    int x = 1;
    int y = 2;
    int z = 0;
    while(x < y)
    {
        x = x + 1;
    }
    sassert(x >= z);
    return 0;
}
