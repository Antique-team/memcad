// Ex array-init: pointer operations on array cells

typedef struct {
  int flag;
  int par;
}me;


void main()
{
  int i = 1;
  me table[30];
  me * ptr = &table[3];
  table[1].flag = table[2].par + 2;
}
