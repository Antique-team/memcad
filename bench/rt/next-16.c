// a small malloc example
// write access off the basis of the edge
typedef struct v {
  int a;
  int b;
} v ;
void main( )
{
  v * x;
  int i;
  x = malloc( 8 );
  i = x->b;
  x->a = 1 + i;
  assert( x->a - x->b == 1 );
}
