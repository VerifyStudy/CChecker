int main()
{
  int x = 0;
  int y = 0;
  while(x < 3)
  {
    x = x + 1;
    y = y + 2;
  }
  if (y < x)
  {
    y = x - y;
  }
  else
  {
    x = y - x;
  }
  sassert(x < y);
}


//Test Structure
void sassert(X) {}

int main()
{
    int a = 0;
    int b = 0;
    if (a > b)
    {
        if (a > b)
        {
            a = 3;
        }
        else
        {
            b = 4;
        }
    }
    else
    {
        if (a > b)
        {
            a = 3;
        }
        else
        {
            b = 4;
        }
    }
    if (a > b)
    {
        a = 3;
    }
    else
    {
        b = 4;
    }
    sassert(a == b);
    return 0;
}


