// Ex prod-sep-00.c :
//    - an example with
//      . int variable, allocated in stack
//      . int* variable, allocated in stack, but their values are allocated in heap
//    - analyzed with a domain [ _ ] * [ ]
//    - some assigns:

void main( ){

  int x ;
  int y ;
  int* xp ;
  int* yp ;
  // main := main
  x = y; 
  assert( x == y );
  // allocation
  xp = malloc( 4 );
  if( xp == 0 )
    exit( 0 );
  // main := main avec pointeur
  yp = xp;
  assert( xp == yp );
  assert( *xp == *yp );  
  yp = malloc( 4 );
  if( yp == 0 )
    exit( 0 );
  // under := under
  *xp = *yp; 
  assert( *xp == *yp );
  // main := under
  x = *yp; 
  assert ( x == *yp );
  // under := main
  *xp = y;
  assert( *xp == y );
}
