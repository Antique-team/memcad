// Ex lcst-04: repeted addition of an element
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
  int i;
  _memcad( "add_inductive( l, lo_wpcst, [ | | ] )" );
  i = 0;
  while( i < 1000 ){
    n = malloc( 8 );
    n->next = l->wl;
    n->stat = l->wi;
    l->wl = n;
    i = i + 1;
  }
  _memcad( "check_inductive( l, lo_wpcst, [ | | ] )" );
}
