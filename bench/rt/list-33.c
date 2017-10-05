// Ex list-33: list, checking refcount management
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list;

void main( ){
  list * lp0 ;
  list * lp1 ;
  list k ;
  lp0 = malloc( 4 );
  lp1 = malloc( 4 );
  if( lp0 == 0 )
    exit( 0 );
  if( lp1 == 0 )
    exit( 0 );
  {
    list l ;
    _memcad( "add_inductive( l, list )" );
    * lp0 = l;
    * lp1 = l;
  }
  * lp0 = NULL;
  k = * lp1;
  _memcad( "check_inductive( k, list )" );
}









