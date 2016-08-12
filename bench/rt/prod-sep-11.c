// Ex prod-sep-11.c :
//    - some operaration on numerical variables
//    - some memory allocation on heap
typedef struct tree {
  struct tree * left ;
  struct tree * right ;
  int data ;  
} tree ;

void main( ){

  int x ;
  int y ;
  int z ;
  tree* t ;
  // num 
  z = x + y ;
  x = z - y + 42;
  y = x * z;
  // heap
  t = malloc( 12 ) ;
  t -> left = null ;
  t -> right = null ;
  t -> data = y ;  

  assert( t -> data == y );
  _memcad( "check_inductive( t, tree )" );
}
