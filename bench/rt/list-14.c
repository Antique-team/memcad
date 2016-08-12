// Ex list-14: inductive introduction (list allocation, no assume)
// - malloc
// - join, unfolding rule
// - join, weaken to inductive rule
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
  l = null;
  m = null;
  while( b ){
    m = malloc( 8 );
    m->next = l;
    m->data = 42;
    l = m;
    m = null;
  }
  _memcad( "check_inductive( l, list )" );
}
