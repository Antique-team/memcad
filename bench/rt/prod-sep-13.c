// Ex prod-sep-13.c :
//    - an example with a large number of variables,
//      where separating conjunction would help
//    - some operaration on numerical variables
//    - add/remove of an element of the list (on heap)
typedef struct tree {
  struct tree * lft ;
  struct tree * rgt ;
  int data ;  
} tree ;

void main( ){
  volatile int rand ;

  int x0 ;
  int x1 ;
  int x2 ;
  int x3 ;
  int x4 ;
  int x5 ;
  int x6 ;
  int x7 ;
  int x8 ;
  int x9 ;

  int y ;
  int z ;

  tree* t ;
  _memcad( "add_inductive( t, tree )" );
    
  y = ( x0 + x1 ) * (x2 - x3) * ( 2 + x4 * x5 );
  z = ( x5 + x6 ) * (x7 - x8) * ( 2 + x9 * x0 );

  if( z > 0 && rand ){
    tree* t0 ;
    // insert left in t
    t0 = t;
    t = malloc( 12 ) ;
    if( t == 0 )
      exit( 0 );
    t -> rgt = null ;
    t -> lft = t0 ;
    t -> data = y ;
  } else {
    if( y > 0 && t != null ){
      // remove
      tree* t0 ;
      t0 = t -> lft ;
      free( t ) ; // there is a memory leak at that point
      t = t0 ;
    }
  }

  _memcad( "check_inductive( t, tree )" );
}
