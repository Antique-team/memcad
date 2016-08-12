// Ex lcst-07: removal of arbitrary elements in the body
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
  wlist l;
  list n;
  int p;
  _memcad( "add_inductive( l, lo_wpcst, [ | | ] )" );
  n = l->wl;
  while( n != null ){
    if( p ){
      if( n->next != null ){
        n->next = n->next->next;
      }
    }
    n = n->next;
  }
  _memcad( "check_inductive( l, lo_wpcst, [ | | ] )" );
}
