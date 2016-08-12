// a loop that does not quite work yet: threshold problem to solve
void main( )
{
  int x ;
  x = 0 ;
  while( x < 12 ){
    x = x + 1 ;
    assert( x < 13 );
  }
  assert( x <= 12 );
  assert( x >= 12 );
}
