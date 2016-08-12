// a small malloc example
// write access off the basis of the edge
typedef struct v {
  int a;
} v ;
void main( )
{
  v * x;
  x = malloc( 4 );
  x->a = 10;
  assert( x->a == 10 );
}
