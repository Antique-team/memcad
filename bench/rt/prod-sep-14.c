// Ex prod-sep-14.c :
//    - an example with a large number of variables,
//      where separating conjunction would help
//    - some operaration on numerical variables
//    - rotate element
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
  tree* t0 ;
  _memcad( "add_inductive( t, tree )" );
    
  y = ( x0 + x1 ) * (x2 - x3) * ( 2 + x4 * x5 );
  z = ( x5 + x6 ) * (x7 - x8) * ( 2 + x9 * x0 );

  if( t!= null && rand ){
    t0 = t -> lft;
    if( t0 != null && rand ){
      t -> lft = t0 -> lft ;
      t0 -> lft = t -> rgt ;
      t -> rgt = t0 -> rgt ;
      t0 -> rgt = t0 -> lft ;
      t0 -> lft = t;
      t = t0 ;
    }
  }

  _memcad( "check_inductive( t, tree )" );
}
