// Ex shape-less-10:
//  code manipulating shape-less memory, i.e., no inductive structure

typedef struct {
  int x;
  int y;
} t;

void f( int * p, int a, int b ){
  if( *p <= a ){
    *p = a;
  } else if( *p >= b ){
    *p = b;
  }
}

void g( t * r, int xa, int xb, int ya, int yb ){
  int * p0;
  int * p1;
  p0 = &(r->x);
  p1 = &(r->y);
  f( p0, xa, xb );
  f( p1, ya, yb );
}

void main( ){
  t t0;
  g( & t0, -10, 10, -5, 15 );
  assert( -10 <= t0.x );
  assert( t0.x <= 10 );
  assert( -5 <= t0.y );
  assert( t0.y <= 15 );
}
