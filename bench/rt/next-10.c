// a small malloc example
void main( )
{
  int * x;
  x = malloc( 4 );
  *x = 10;
  assert( *x == 10 );
}
