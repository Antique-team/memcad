// Ex prod-sep-03.c :
//    - an example with a large number of variables,
//      where separating conjunction would help
//    - some operaration on numerical variables
//    - add/remove of an element of the list (on heap)
typedef struct list {
  struct list * next ;
  int data ;  
} list ;

void main( ){
  volatile int x0 ;
  volatile int x1 ;
  volatile int x2 ;
  volatile int x3 ;
  volatile int x4 ;
  volatile int x5 ;
  volatile int x6 ;
  volatile int x7 ;
  volatile int x8 ;
  volatile int x9 ;

  int y ;
  int z ;

  list* q ;
  _memcad( "add_inductive( q, list )" );
    
  y = ( x0 + x1 ) * (x2 - x3) * ( 2 + x4 * x5 );
  z = ( x5 + x6 ) * (x7 - x8) * ( 2 + x9 * x0 );

  if( z > 0 ){
    list* q0 ;
    // insert in q
    q0 = q;
    q = malloc( 8 ) ;
    q -> next = q0 ;
    q -> data = y ;
  } else {
    if( y > 0 && q != null ){
      // remove from q
      list* q0 ;
      q0 = q -> next;
      free( q );
      q = q0;
    }
  }

  _memcad( "check_inductive( q, list )" );
}
