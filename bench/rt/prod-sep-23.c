// Ex prod-sep-23.c : allocation in a loop
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

  volatile int rand;
  int i0 ;
  list* l0 ;
  list* l1 ;
  tree* t0 ;
  tree* t1 ;
  
  l0 = null;
  t0 = null;
  i0 = 0;

  while( rand ){    
    _memcad( "check_inductive( l0, list )" );
    _memcad( "check_inductive( t0, bintree_o )" );    
    if( rand ){ // list alloc
      l1 = malloc( 8 );
      l1 -> n = l0;
      l1 -> id = i0;
      i0 = i0 + 1;
      l0 = l1;
    }
    if( rand ){ // tree alloc
      t1 = malloc( 12 );
      t1 -> l = t0;
      t1 -> r = null;
      t1 -> d = -1;
      t0 = t1;
    }    
  }
  _memcad( "check_inductive( l0, list )" );
  _memcad( "check_inductive( t0, bintree_o )" );
}
