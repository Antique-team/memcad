// Ex list-22: list traversal + step from initial (two cursors)
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l;
  list c;
  list d;
  _memcad( "add_inductive( l, list )" );
  c = l;
  d = null;
  while( c != 0 ){
    c = c->next ;
  }
  if( l != null ){
    d = l->next;
  }
  _memcad( "check_inductive( c, list )" );
  _memcad( "check_inductive( d, list )" );
  _memcad( "check_inductive( l, list )" );
}
