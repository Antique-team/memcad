// Demo-1: a few list algorithms
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
// list allocation function
list allocate( int n ){
  list m;
  int b;
  m = null;
  while( b < n ){
    list k;
    k = malloc( 8 );
    k->next = m;
    k->data = 0;
    m = k;
  }
  return m;
}
// list deallocation function
void deallocate( list l ){
  list m;
  m = l;
  while( m != null ){
    list k;
    k = m->next;
    free( m );
    m = k;
  }
}
// list traversal (e.g. printing)
void iter( list l ){
  list c;
  c = l;
  while( c != null ){
    c = c->next;
    _memcad( "check_inductive( c, list )" );
  }
}
//
void main( ){
  int a;
  list ll;
  // allocation
  ll = allocate( a );
  // first structural test
  _memcad( "check_inductive( ll, list )" );
  // reversal
  {
    list k;
    list r;
    r = null;
    while( ll != null ){
      k = ll->next;
      ll->next = r;
      r = ll;
      ll = k;
    }
    ll = r;
  }
  // iteration over the structure
  iter( ll );
  // structural check
  _memcad( "check_inductive( ll, list )" );
  // deallocation
  deallocate( ll );
}
