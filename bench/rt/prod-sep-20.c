// Ex prod-sep-20.c : list and tree
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

  l = malloc( 8 );
  if( l == 0 )
    exit( 0 );
  l -> n = null ;
  l -> id = rand;
  
  t = malloc( 12 );
  if( t == 0 )
    exit( 0 );
  t -> l = null ;
  t -> r = null ;
  t -> d = rand ;

  _memcad( "check_inductive( l, list )" );
  _memcad( "check_inductive( t, bintree_o )" );
}
