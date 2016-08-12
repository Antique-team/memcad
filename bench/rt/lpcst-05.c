// Ex lcst-05: free
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
  list n;
  int * p;
  _memcad( "add_inductive( l, lo_wpcst, [ | | ] )" );
  while( l->wl != null ){
    n = l->wl;
    l->wl = n->next;
    free( n );
  }
  // issue with this free: the analyzer does not see p as an allocated node
  //p = l->wi;
  //free( p );
  free( l );
}
