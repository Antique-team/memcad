// Ex todo-01: list reversal
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  list k ;
  _memcad( "add_inductive( l, slllo )" );
  r = null;
  k = null; // nullify, to discard constraint, to remove
  _memcad( "add_inductive( r, slllo )" );
  while( l != 0 ){
    k = l->next;
    l->next = r;
    r = l;
    l = k;
    k = null; // nullify, to discard constraint, to remove
  }
  _memcad( "check_inductive( l, slllo )" );
}
