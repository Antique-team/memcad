// Ex shape-less-16:
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
  t t3;
  t t4;
  t t5;
  t t6;
  t t7;
  t t8;
  t t9;
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
  if( rand ){
    t3.x = 0;
    t3.y = 0;
  } else {
    t3.x = 1;
    t3.y = 2;
  }
  t.x = t.x + t3.x;
  t.y = t.y + t3.y;
  if( rand ){
    t4.x = 0;
    t4.y = 0;
  } else {
    t4.x = 1;
    t4.y = 2;
  }
  t.x = t.x + t4.x;
  t.y = t.y + t4.y;
  if( rand ){
    t5.x = 0;
    t5.y = 0;
  } else {
    t5.x = 1;
    t5.y = 2;
  }
  t.x = t.x + t5.x;
  t.y = t.y + t5.y;
  if( rand ){
    t6.x = 0;
    t6.y = 0;
  } else {
    t6.x = 1;
    t6.y = 2;
  }
  t.x = t.x + t6.x;
  t.y = t.y + t6.y;
  if( rand ){
    t7.x = 0;
    t7.y = 0;
  } else {
    t7.x = 1;
    t7.y = 2;
  }
  t.x = t.x + t7.x;
  t.y = t.y + t7.y;
  if( rand ){
    t8.x = 0;
    t8.y = 0;
  } else {
    t8.x = 1;
    t8.y = 2;
  }
  t.x = t.x + t8.x;
  t.y = t.y + t8.y;
  if( rand ){
    t9.x = 0;
    t9.y = 0;
  } else {
    t9.x = 1;
    t9.y = 2;
  }
  t.x = t.x + t9.x;
  t.y = t.y + t9.y;
  // check-up assertions
  assert( 0 <= t.x );
  assert( t.x <= 10 );
  assert( 0 <= t.y );
  assert( t.y <= 20 );
}
