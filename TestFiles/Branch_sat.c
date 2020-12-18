//SAFE
void sassert(X) {}

int main()
{
	int b = 0;
	int a = b - 1;
	while (b < 8)
	{
		b = b + 1;
		if (b == 8)
		{
			a = 1;
		}
		else
		{
		}
	}
	sassert(a > 0);
	return 0;
}
