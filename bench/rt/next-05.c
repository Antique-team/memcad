// some basic arithmetic tests
void main( )
{
  int x ;
  if( x < 10 ){
    assert( x != 12 );
  } else if( x > 10 ){
    assert( x != -5 );
  } else {
    assert( x == 10 );
  }
}
