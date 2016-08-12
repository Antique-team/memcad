// Ex lcst-00: lcst ptr copy
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  _memcad( "add_inductive( l, lo_icst, [ |42| ] )" );
  r = l;
  _memcad( "check_inductive( r, lo_icst, [ |42| ] )" );
}
