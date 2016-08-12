// Ex prod-sep-06.c :
// - create empty list, check structure
// - add 1 element, check structure
typedef struct list {
  struct list * next ;
  int data ;  
} list ;

void main( ){

  int x ;
  int y ;
  int z ;
  int t ;
  // num
  z = x + y ;
  t = x * y ;
  // heap
  list* q;
  q = NULL;
  // check
  _memcad( "check_inductive( q, list )" );
  q = malloc( 8 );
  q -> next = NULL;
  q -> data = t - z;
  // check
  _memcad( "check_inductive( q, list )" );
}
