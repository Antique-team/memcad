// Ex prod-sep-01.c :
//    - an example with a large number of variables,
//      where separating conjunction would help
//    - some operaration on numerical variables
//    - some memory allocation on heap
typedef struct list {
  struct list * next ;
  int data ;  
} list ;

void main( ){

  int x ;
  int y ;
  int z ;
  int t ;
  list* q ;
  // num 
  z = x + y ;
  t = x - y ;
  // heap
  q = malloc( 8 ) ;
  if( q == 0 )
    exit( 0 );
  q -> next = null ;
  q -> data = z ;  

  assert( q -> data == z );
  assert( q -> data == t + 2 * y );
  _memcad( "check_inductive( q, list )" );
}
