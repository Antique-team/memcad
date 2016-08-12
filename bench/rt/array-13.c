// Ex array-13: a loop of test for widen and inclusion check

typedef struct {
  int flag;
  int par;
} me;


void main()
{
  me table[30];
  int i = 0;
  table[i].flag = 0;
  i = 1;
  while (i < 30)
    {
      table[i].flag = 0;
      i = i + 1;
    }
  int j = 18;
  j = table[j].flag;
  assert( j == 0);
}
