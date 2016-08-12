// Ex prod-sep-10.c
typedef struct tree {
  struct tree * left ;
  struct tree * right ;
  int data ;  
} tree ;

void main( ){

  tree* t;
  // one tree node
  t = malloc( 12 ) ;
  t -> left = null ;
  t -> right = null ;
  t -> data = -1 ;  

  _memcad( "check_inductive( t, tree )" );
}
