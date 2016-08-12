// Ex prod-sep-21.c : list and tree
typedef struct list {
  struct list * n ;
  int id ;  
} list ;
typedef struct tree {
  struct tree * l ;
  struct tree * r ;
  int d ;  
} tree ;

void main( ){

  list* l ;
  tree* t ;
  volatile int rand ;

  _memcad( "add_inductive( l, list )" );
  _memcad( "add_inductive( t, bintree_o )" );

  if( l != null ){
    if( t != null ){
      l -> id = t -> d;
    }
  }

  _memcad( "check_inductive( l, list )" );
  _memcad( "check_inductive( t, bintree_o )" );
}
