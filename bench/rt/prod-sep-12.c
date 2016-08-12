// Ex prod-sep-12.c :
//    - some operaration on numerical variables
//    - inductive assumption on heap
typedef struct tree {
  struct tree * left ;
  struct tree * right ;
  int data ;  
} tree ;

void main( ){

  int x ;
  int y ;
  int z ;
  int t ;
  tree* tr ;
  // num
  z = x - y ;
  t = x * y ;
  // heap
  _memcad( "add_inductive( tr, tree )" );
  // check
  _memcad( "check_inductive( tr, tree )" );
}
