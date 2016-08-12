// Ex llen-02: llen extension
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  _memcad( "add_inductive( l, slllo, [ |100| ] )" );
  r = malloc( 8 );
  r->next = l;
  _memcad( "check_inductive( r, slllo, [ |101| ] )" );
}
