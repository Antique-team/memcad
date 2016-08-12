// Ex array-14: arrays and loops
int test[100];
void main()
{
  int i;
  int tmp;
  i = 0;
  test[i] = 5;
  i = i + 1;
  while( i < 100)
    {
      test[i] = 5;
      i = i + 1;
    }
  i = 0;
  while( i < 100)
    {
      tmp = test[i];
      assert(tmp == 5);
      i = i + 1;
    }

}
