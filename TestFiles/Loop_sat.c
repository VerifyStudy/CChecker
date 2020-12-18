//SAFE
void sassert(X){}

int main()
{
    int x = 1;
    int y = 2;
    int z = 0;
    while(x < y)
    {
        x = x + 1;
    }  
    sassert(x >= z);
    return 0;
}
