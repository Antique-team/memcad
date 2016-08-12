// Ex lcst-00: lcst ptr copy
typedef struct elist {
  struct elist * next ;
  int * stat ;
} elist ;
typedef elist * list;
typedef struct ewlist {
  list * wl;
  int * wi;
} ewlist;
typedef ewlist * wlist;
void main( ){
  wlist l ;
  wlist r ;
  _memcad( "add_inductive( l, lo_wpcst, [ | | ] )" );
  r = l;
  _memcad( "check_inductive( r, lo_wpcst, [ | | ] )" );
}
