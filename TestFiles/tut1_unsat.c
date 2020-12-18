//UNSAFE
void sassert(X) {}

int main()
{
	int x = 1;
	int y = 0;
	if (x > y)
	{
		x = y - x;
		sassert(x > 0);
	}
	else
	{
		
	}
	return 0;
}
