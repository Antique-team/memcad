// Ex list-27: list traversal + join torture test
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
volatile int cond;
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
  if( cond ){
    c = c;
  } else {
    c = c;
  }
  // not sure why is c considered live here!
  _memcad( "check_inductive( l, list )" );
}
