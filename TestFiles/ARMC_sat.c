//SAFE
void sassert(X){}

int main()
{
    int x = 1;
    int y = 0;
    while(x <= 10)
    {
        x = x + 1;
        y = y + 1;
    }  
    sassert(x == y);
    return 0;
}
