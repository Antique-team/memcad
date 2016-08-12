// Ex shape-less-17:
//  code manipulating shape-less memory, i.e., no inductive structure

typedef struct t {
  int x;
  int y;
} t;

void main( ){
  t t;
  struct t * p;
  int * q;
  p = & t;
  // init x
  q = & (p->x);
  *q = 0;
  // init y
  q = & (p->y);
  *q = 0;
  // assertions checks
  assert( t.x == 0 );
  assert( t.y == 0 );
}
