//UNSAFE
void sassert(X) {}

int main()
{
    int i;
    int x;
    int y;
    y = 7;
    x = 0;

    if (y == 7)
    {
        x = 5;
        i = 1;
        while ( i < 100000)
        {
            y++;
            i++;
        }
        sassert( x == 5);
    }
    else
    {}

    return 0;
}
