// Ex list-13: list traversal
typedef struct elist {
  struct elist * next;
  int data;
} elist;
typedef elist * list;
void traverse( list la ){
  list c;
  c = la;
  while( c != 0 ){
    c = c->next;
  }
  _memcad( "check_inductive( c, list )" );
}
void main( ){
  list l;
  _memcad( "add_inductive( l, list )" );
  traverse( l );
  _memcad( "check_inductive( l, list )" );
}
