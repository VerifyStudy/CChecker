//UNSAFE
void sassert(X) {}

void main()
{
    int x, y;
    int i;

    x = 6;

    for (i = 1; i < 100000; i++)
    {
        // x++;
        y++;
    }

    assert (x != 5);
}
