//UNSAFE
void sassert(X) {}

void main()
{
	int x;
	int y;
	int k = 3;
	x = 0;
	y = 0;
	while (k > 0)
	{
		x++;
		y++;
		k--;
	}
	while (x > 0)
	{
		x--;
		y--;
	}
	sassert(y == 0);
	return 0;
}
