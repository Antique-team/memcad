void main( )
{
  int x ;
  x = 0 ;
  while( x < 10 ){
    x = x + 1 ;
    assert( x < 11 );
  }
  assert( x <= 10 );
  assert( x >= 10 );
}
