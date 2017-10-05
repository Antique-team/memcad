// Ex list-21: inductive introduction (list allocation, no assume)
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
  if( k == 0 )
    exit( 0 );
  k->next = null;
  k->data = 24;
  l = k;
  m = null;
  while( b ){
    m = malloc( 8 );
    if( m == 0 )
      exit( 0 );
    m->next = l;
    m->data = 42;
    l = m;
  }
  list ln;
  ln = l;
  while (ln->next != null) {
    ln = ln->next;
  }
  _memcad( "check_inductive( l, list )" );
  _memcad( "check_inductive( ln, list )" );
  _memcad( "check_inductive( k, list )" );
}
