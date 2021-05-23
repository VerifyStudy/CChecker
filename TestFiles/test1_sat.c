//UNSAFE
void sassert(X) {}

void main()
{
    int i;
    int x;
    int y;

    x = 6;

    for (i = 1; i < 100000; i++)
    {
        // x++;
        y++;
    }

    sassert (x != 6);
}
