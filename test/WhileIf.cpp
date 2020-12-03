int main()
{
  int x = 0;
  int y = 0;

  while(x < 3)
  {
    x = x + 1;
    y = y + 1;
    if (x < 4)
    {
      x++;
    }
    else
    {
      x--;
    }
    y = 7;
  }
}
