// Ex prod-sep-04.c :
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
  list* q0 ;
  _memcad( "add_inductive( q, list )" );
    
  y = ( x0 + x1 ) * (x2 - x3) * ( 2 + x4 * x5 );
  z = ( x5 + x6 ) * (x7 - x8) * ( 2 + x9 * x0 );

  if( z > 0 ){
    // insert in q
    q0 = malloc( 8 ) ;
    q0 -> next = q ;
    q0 -> data = y ;
    q = q0;
  }else{
    if( y > 0 && q != null ){
      // remove from q
      q0 = q;
      q = q -> next;
      free( q0 );
    }
  }
  _memcad( "check_inductive( q, list )" );

}
