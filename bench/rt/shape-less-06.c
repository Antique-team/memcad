// Ex shape-less-06:
//  code manipulating shape-less memory, i.e., no inductive structure

typedef struct {
  int a;
  int b;
} t;

void main( ){
  t x;
  int y;
  y = 0;
  if( x.a <= 3 ){
    if( x.b >= 3 ){
      y = x.a - x.b;
    }
  }
  assert( y <= 0 );
}
