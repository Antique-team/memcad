// Ex todo-02: list traversal
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list c ;
  _memcad( "add_inductive( l, slllo, [|100|] )" );
  c = l;
  while( c != 0 ){
    c = c->next ;
  }
  _memcad( "check_inductive( c, slllo, [|0|] )" );
  _memcad( "check_inductive( l, slllo, [|100|] )" );
}
