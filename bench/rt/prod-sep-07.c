// Ex prod-sep-07.c :
// - create list step by step, check structure at each steap
// - check structure at the end
typedef struct list {
  struct list * next ;
  int data ;  
} list ;

void main( ){

  int x ;
  int y ;
  int z ;
  int x0 ;
  int x1 ;
  int x2 ;
  int x3 ;
  int x4 ;
  int x5 ;
  int x6 ;
  int x7 ;
  int x8 ;
  int x9 ;
  volatile int rand;
  x = 1 ;
  y = 1 ;
  // heap
  list* q ;
  _memcad( "add_inductive( q, list )" );
  while( rand ){
    list* q0;
    // num operations
    z = x + y ;
    x = y;
    y = z;
    // check
    _memcad( "check_inductive( q, list )" );
    q0 = malloc( 8 );
    if( q0 == 0 )
      exit( 0 );
    q0 -> next = q;
    q0 -> data = z + x1 * x2 - x3 * x4 + x5;
    q = q0;
  }
  // check
  _memcad( "check_inductive( q, list )" );
}
