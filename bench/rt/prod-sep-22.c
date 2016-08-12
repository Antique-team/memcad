// Ex prod-sep-22.c :
//    - an example with a large number of variables,
//      where separating conjunction would help
//    - some operaration on numerical variables
//    - some memory allocation on heap
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

  int i0 ;
  int i1 ;
  int i2 ;

  list* l0 ;
  list* l1 ;

  tree* t0 ;
  tree* t1 ;

  volatile int rand;

  _memcad( "add_inductive( l0, list )" );
  _memcad( "add_inductive( t0, bintree_o )" );
  // insert in list
  if( l0 != null && rand ){
    l1 = malloc( 8 ) ;
    l1 -> n = l0 ;
    l1 -> id = -1 ;
    if( t0 != null ){ 
      l1 -> id = t0 -> d;
    }
    l0 = l1;
  }
  if( t0!= null && rand ){
    t1 = t0 -> l;
    if( t1 != null && rand ){
      // rotate
      t0 -> l = t1 -> l ;
      t1 -> l = t0 -> r ;
      t0 -> r = t1 -> r ;
      t1 -> r = t1 -> l ;
      t1 -> l = t0;
      t0 = t1 ;
    }else{
      // remove
      t1 = t0;
      t0 = t0 -> r;
      free( t1 );
    }
  }
  
  _memcad( "check_inductive( l0, list )" );
  _memcad( "check_inductive( t0, bintree_o )" );
}
