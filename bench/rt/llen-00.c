// Ex llen-00: llen ptr copy
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  _memcad( "add_inductive( l, slllo, [ |100| ] )" );
  r = l;
  _memcad( "check_inductive( r, slllo, [ |100| ] )" );
}
