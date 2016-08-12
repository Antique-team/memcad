// Ex list-01: list reversal
typedef struct elist {
  int data0 ;
  struct elist * next ;
  int data1 ;
  int data2 ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  list k ;
  _memcad( "add_inductive( l, list36 )" );
  r = null;
  k = null; // nullify, to discard constraint, to remove
  _memcad( "add_inductive( r, list36 )" );
  while( l != 0 ){
    k = l->next;
    l->next = r;
    r = l;
    l = k;
    k = null; // nullify, to discard constraint, to remove
  }
  _memcad( "check_inductive( l, list36 )" );
}
