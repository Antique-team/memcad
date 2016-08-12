// Ex list-15: inductive introduction (list allocation, no assume)
// => though, this version has a memory leak
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
  list k;
  list m;
  int b;
  k = malloc( 8 );
  k->next = null;
  k->data = 24;
  l = k;
  m = null;
  while( b ){
    m = malloc( 8 );
    m->next = k;
    m->data = 42;
    l = m;
    m = null;
  }
  _memcad( "check_inductive( l, list )" );
}
