// Ex lcst-02: lcst step + join
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l ;
  list r ;
  list m ;
  _memcad( "add_inductive( l, lo_icst, [ |32| ] )" );
  if( l != null ){
    r = l;
    m = r->next;
    _memcad( "check_inductive( m, lo_icst, [ |32| ] )" );
    assert( r->data == 32 );
  }
}
