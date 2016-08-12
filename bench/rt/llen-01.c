// Ex llen-01: llen step
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  list m ;
  _memcad( "add_inductive( l, slllo, [ |100| ] )" );
  r = l;
  m = r->next;
  _memcad( "check_inductive( m, slllo, [ |099| ] )" );
}
