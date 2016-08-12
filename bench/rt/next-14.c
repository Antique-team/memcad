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
  y = x->a;
  x->b = y;
  assert( x->a - x->b == 0 );
}
