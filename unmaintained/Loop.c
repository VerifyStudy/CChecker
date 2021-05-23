void sassert(X) {}
void assume(X) {}
int main()
{
	int a = 0;
	int b = 0;
	assume(b == 0);
	while (a == b)
	{
		a = a + 1;
		b = b + 1;
	}
	sassert(a != b);
	return 0;
}