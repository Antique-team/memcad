// Ex shape-less-10:
//  code manipulating shape-less memory, i.e., no inductive structure

typedef struct str_t {
  int x;
  int y;
} t;

typedef t * p_t;
typedef int * p_int;

void f( p_int p, int a, int b ){
  if( *p <= a ){
    *p = a;
  } else if( *p >= b ){
    *p = b;
  }
}

void g( p_t r, int xa, int xb, int ya, int yb ){
  f( &(r->x), xa, xb );
  f( &(r->y), ya, yb );
}

void main( ){
  t t0;
  t t1;
  g( & t0, -10, 10, -5, 15 );
  assert( -10 <= t0.x );
  assert( t0.x <= 10 );
  assert( -5 <= t0.y );
  assert( t0.y <= 15 );
}
