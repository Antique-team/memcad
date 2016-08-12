// Ex prod-sep-02.c :
//    - an example with a large number of variables,
//      where separating conjunction would help
//    - some operaration on numerical variables
//    - inductive assumption on heap
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
  z = x - y ;
  t = x * y ;
  // heap
  list* q ;
  _memcad( "add_inductive( q, list )" );
  // check
  _memcad( "check_inductive( q, list )" );
}
