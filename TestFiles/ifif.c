//Test Structure
void sassert(X) {}

int main()
{
    int a = 0;
    int b = 0;
    if (a > b)
    {
        if (a > b)
        {
            a = 3;
        }
        else
        {
            b = 4;
        }
    }
    else
    {
        if (a > b)
        {
            a = 3;
        }
        else
        {
            b = 4;
        }
    }
    if (a > b)
    {
        a = 3;
    }
    else
    {
        b = 4;
    }
    sassert(a == b);
    return 0;
}
