// Ex list-29: testing unfold lvalue
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
  if( l != null ){
    _memcad( "unfold( l )" );
    _memcad( "unfold( l->next )" );
    c = l->next;
    _memcad( "check_inductive( c, list )" );
  }
}
