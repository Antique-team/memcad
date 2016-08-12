// Ex lcst-03: adding an element
typedef struct elist {
  struct elist * next ;
  int * stat ;
} elist ;
typedef elist * list;
typedef struct ewlist {
  list wl;
  int * wi;
} ewlist;
typedef ewlist * wlist;
void main( ){
  wlist l ;
  wlist r ;
  list n;
  _memcad( "add_inductive( l, lo_wpcst, [ | | ] )" );
  r = malloc( 8 );
  r->wl = l->wl;
  r->wi = l->wi;
  n = malloc( 8 );
  n->next = l->wl;
  n->stat = r->wi;
  r->wl = n;
  _memcad( "check_inductive( r, lo_wpcst, [ | | ] )" );
  _memcad( "check_inductive( l, lo_wpcst, [ | | ] )" );
}
