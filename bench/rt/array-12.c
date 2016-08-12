// Ex array-12: A basic test for join mainly create.

typedef struct {
  int flag;
  int par;
} me;


void main()
{
  me table[30];
  int i = 1;
  int j;
  if (j > 9)
    table[i].flag = 1;
    table[i].par = 10;
  j = table[i].par;
  assert ((j < 11));
}
