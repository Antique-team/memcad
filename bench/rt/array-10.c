// Ex array-10: test for join, mainly merge_phase

typedef struct {
  int flag;
  int par;
} me;


void main()
{
  me table[30];
  int i ;
  int j ;
  int k;
  j = 1;
  k = 2;
  if (i > 0)
    {
    table[j].flag = 1;
    table[k].flag = 1;
    }
  else
    table[j].flag = 1;
  i = table[j].flag;
  assert(i >= 0);
}
