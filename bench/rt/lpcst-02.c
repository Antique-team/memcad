// Ex lcst-02: lcst contents copy
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
  _memcad( "add_inductive( l, lo_wpcst, [ | | ] )" );
  r = malloc( 8 );
  r->wl = l->wl;
  r->wi = l->wi;
  if( r->wl != null ){
    r->wl = r->wl->next;
    _memcad( "check_inductive( r, lo_wpcst, [ | | ] )" );
  }
}
