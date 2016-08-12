// Ex shape-less-18:
//  code manipulating shape-less memory, i.e., no inductive structure

typedef struct {
  int x;
  int y;
} t;

void main( ){
  t * p;
  t * q;
  p = malloc( 8 );
  q = malloc( 8 );
  p->x = 4;
  if( p->y < -10 ){
    p->y = -10;
  } else if( p->y > 10 ){
    p->y = 10;
  }
  q->x = p->x + p->y;
  free( p );
  // check-up assertions
  assert( -6 <= q->x );
  assert( q->x <= 14 );
}
