// Ex list-11: random list construction
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list c ;
  list m ;
  int b;
  _memcad( "add_inductive( l, list )" );
  c = l;
  while( c != 0 ){
    if( b ){
      m = malloc( 8 ) ;
      m->next = c->next ;
      m->data = 0;
      c->next = m;
    } 
    c = c->next;
  }
  _memcad( "check_inductive( c, list )" );
  _memcad( "check_inductive( l, list )" );
}
