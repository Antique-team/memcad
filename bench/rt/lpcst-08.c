// Ex lcst-08: removal of arbitrary elements
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
  int p;
  int b;
  b = 0;
  _memcad( "add_inductive( l, lo_wpcst, [ | | ] )" );
  if( p ){
    if( l->wl != null ){
      b = 1;
    }
  }
  if( b == 1 ){
    // removal of the first element
    l->wl = l->wl->next;
  } else {
    // removal of an element in the body
    list n;
    n = l->wl;
    while( n != null ){
      if( p && n->next != null ){
        n->next = n->next->next;
      }
      n = n->next;
    }
  }
  _memcad( "check_inductive( l, lo_wpcst, [ | | ] )" );
}
