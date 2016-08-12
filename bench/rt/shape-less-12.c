// Ex shape-less-12:
//  code manipulating shape-less memory, i.e., no inductive structure

typedef struct {
  int x;
  int y;
} t;

void f_zero( t * x ){
  x->x = 0;
  x->y = 0;
}

void f_set( t * x, int a, int b ){
  x->x = a;
  x->y = b;
}

void f_add( t * x, t * y ){
  x->x = x->x + y->x;
  x->y = x->y + y->y;
}  

volatile int rand;

void main( ){
  // stress testing join (for perf)
  t t0;
  t t;
  // add several randomly chosen vectors
  f_zero( & t );
  if( rand )
    f_zero( & t0 );
  else
    f_set( & t0, 1, 2 );
  f_add( & t, & t0 );
  // check-up assertions
  assert( 0 <= t.x );
  assert( t.x <= 5 );
  assert( 0 <= t.y );
  assert( t.y <= 10 );

}
