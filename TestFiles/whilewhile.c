//Test Structure
void sassert(X) {}

int main()
{
    int a = 4;
    while (a > 4)
    {
        while (a > 4)
        {
            a = 5;
        }
    }
    while (a > 4)
    {
        a = 5;
    }
    sassert(a == a);
    return 0;
}