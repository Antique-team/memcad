// Ex array-11: basic access to array cells
//  (to identify failure point in dom_mem_flat)

typedef struct {
  int flag;
  int par;
} me;


void main()
{
  me hello;
  me table[30];
  int i = 0;
  int j = 1;
  int k;
  table[i].par = 10;
  table[j].par = 4;
  table[i].flag = table[i].par + table[i].par+2;
  if (k < 2 )
    {
      if ( k > -1)
	{
	  table[k].flag = 5;
	  k = table[i].par + table[k].flag;
	  assert( k <= 16  );
	}
    }
  
}
