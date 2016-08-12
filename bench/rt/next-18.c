// a small malloc example
// write access off the basis of the edge
typedef struct v {
  int a;
  int b;
} v ;
void main( )
{
  v * x;
  int y;
  x = malloc( 8 );
  y = 42;
  x->b = y;
  x->a = y;
  y = x->a - x->b;
  free( x );
  assert( y == 0 );
}
