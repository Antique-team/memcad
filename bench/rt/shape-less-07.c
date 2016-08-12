// Ex shape-less-07:
//  code manipulating shape-less memory, i.e., no inductive structure

typedef struct {
  int a;
  int b;
} t;

void main( ){
  t x;
  t * y;
  int z;
  y = & x;
  x.a = 24;
  z = y->a + 1;
  assert( y->a <= 28 );
  assert( z == 25 );
}
