int main()
{
	int x = 0;
	int y = 0;
	while (x < 3)
	{
		x = x + 1;
		y = y + 1;
		if (x > 6)
		{
			x = 4;
		}
		else
		{
			y = 0;
		}
	}
	if (x == 3)
	{
		while (x == 3)
		{
			y = x;
		}
	}else
	{

	}
	return 0;
}
