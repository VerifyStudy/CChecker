//SAFE
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
