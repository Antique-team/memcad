// Ex list-08: list traversal
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list c ;
  _memcad( "add_inductive( l, list )" );
  c = l;
  while( c != 0 ){
    c = c->next ;
  }
  _memcad( "check_inductive( c, list )" );
  _memcad( "check_inductive( l, list )" );
}
