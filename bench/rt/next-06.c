// some basic arithmetic tests
void main( )
{
  int x ;
  int y ;
  if( y < 50 ){
    if( x < y + 1 ){
      assert( x < 60 );
    } else if( x < y - 1 ){
      assert( 0 );
    }
  } else {

  }
}
