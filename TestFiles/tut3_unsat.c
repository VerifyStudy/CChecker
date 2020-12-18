//UNSAFE
void sassert(X) {}

void main()
{
	int x, y;
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
	assert(y == 0);
	return 0;
}
