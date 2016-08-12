// Ex shape-less-13:
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
  t t1;
  t t2;
  t t;
  // add several randomly chosen vectors
  t.x = 0;
  t.y = 0;
  if( rand ){
    t0.x = 0;
    t0.y = 0;
  } else {
    t0.x = 1;
    t0.y = 2;
  }
  t.x = t.x + t0.x;
  t.y = t.y + t0.y;
  if( rand ){
    t1.x = 0;
    t1.y = 0;
  } else {
    t1.x = 1;
    t1.y = 2;
  }
  t.x = t.x + t1.x;
  t.y = t.y + t1.y;
  if( rand ){
    t2.x = 0;
    t2.y = 0;
  } else {
    t2.x = 1;
    t2.y = 2;
  }
  t.x = t.x + t2.x;
  t.y = t.y + t2.y;
  // check-up assertions
  assert( 0 <= t.x );
  assert( t.x <= 3 );
  assert( 0 <= t.y );
  assert( t.y <= 6 );
}
