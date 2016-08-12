// Ex lcst-03: lcst extension
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  _memcad( "add_inductive( l, lo_icst, [ |72| ] )" );
  r = malloc( 8 );
  r->next = l;
  r->data = 72;
  _memcad( "check_inductive( r, lo_icst, [ |72| ] )" );
}
