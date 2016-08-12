// Ex list-07: allocation of a list
// - malloc
// - join, with unfolding rule
// -> disjunction domain turned off, in order to force the join
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l;
  list m;
  int b;
  _memcad( "add_inductive( l, list )" );
  m = null;
  while( b ){
    m = malloc( 8 );
    m->next = l;
    m->data = 0;
    l = m;
    m = null;
  }
  _memcad( "check_inductive( l, list )" );
}
