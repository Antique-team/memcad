// Ex prod-sep-24.c : allocation in a loop
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
  int i1 ;
  int i2 ;
  list* l0 ;
  list* l1 ;
  tree* t0 ;
  tree* t1 ;
  tree* t2 ;
  
  l0 = null;
  t0 = null;
  i0 = 0;
  i1 = 0;

  while( rand ){    
    _memcad( "check_inductive( l0, list )" );
    _memcad( "check_inductive( t0, bintree_o )" );    
    if( rand ){ // list alloc
      l1 = malloc( 8 );
      if( l1 == 0 )
        exit( 0 );
      l1 -> n = l0;
      l1 -> id = i0;
      i0 = i0 + 1;
      l0 = l1;
    }
    if( l0 != null && rand ){
      // pick an element in the list
      l1 = l0 ;
      l0 = l0 -> n ;
      i2 = l1 -> id ;
      free( l1 ) ;
      // create tree node
      i1 = i1 + 1 ;
      t1 = malloc( 12 ) ;
      if( t1 == 0 )
        exit( 0 );
      t1 -> d = i1 * i2 ;
      // insert it in the tree
      if( t0 == null ){
        t0 = t1 ;
        t0 -> l = null;
        t0 -> r = null;
      }else{
        t2 = t0 ;
        assert( t2 != null );
        while( t2 -> r != null ){
          t2 = t2 -> r;
        }
        assert( t2 -> r == null );        
        t2 -> r = t1 ;
        t1 -> l = null;
        t1 -> r = null;
      }      
    }    
  }
  _memcad( "check_inductive( l0, list )" );
  _memcad( "check_inductive( t0, bintree_o )" );
}
