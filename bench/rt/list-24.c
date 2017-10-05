// Ex list-24: double list traversal, force_live command
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l;
  list k;
  list m;
  volatile int b;
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
  // while (ln != k) {
  while( ln->next != null ){
    ln = ln->next;
  }
  // assert( ln == k );
  if( ln == k ){
    // hack to check the empty segment was generated
    _memcad( "check_bottomness( false )" );
  }
  m = ln->next;
  //_memcad( "unfold( m )" );
  _memcad( "check_bottomness( false )" );
  _memcad( "force_live( l, ln, k )" );
  _memcad( "check_inductive( l, list )" );
}
