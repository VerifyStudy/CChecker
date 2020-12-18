//Test Structure
void sassert(X) {}

int main()
{
	int x = 0;
	int y = 0;

	while (x < 3)
	{
		x = x + 1;
		y = y + 1;
		if (x < 4)
		{
			x = x + 1;
		}
		else
		{
			x = x - 1;
			sassert(x == 6);
		}
		y = 7;
	}
	return 0;
}
