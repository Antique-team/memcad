// Ex list-04: two concurrent list reversals
// double version of the c-micro-03 example
// two lists reversed in the same time (one completely, one partly)
// this code tests a more exhaustive form of weak abstraction that
// that of c-micro-03
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l0 ;
  list l1 ;
  list r ;
  list k ;
  _memcad( "add_inductive( l0, list )" );
  _memcad( "add_inductive( l1, list )" );
  r = null;
  k = null; // nullify, to discard constraint, to remove
  _memcad( "add_inductive( r, list )" );
  while( l0 != 0 && l1 != 0 ){
    k = l0->next;
    l0->next = r;
    r = l0;
    l0 = k;
    k = l1->next;
    l1->next = r;
    r = l1;
    l1 = k;
    k = null; // nullify, to discard constraint, to remove
  }
  _memcad( "check_inductive( l0, list )" );
  _memcad( "check_inductive( l1, list )" );
  _memcad( "check_inductive( r, list )" );
}
