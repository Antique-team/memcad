// Ex list-16: inductive introduction (list allocation, no assume)
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
    m->next = l;
    m->data = 42;
    l = m;
  }
  k = k ; // Hack, to remove to check for more robust algorithms
  _memcad( "check_inductive( l, list )" );
}
