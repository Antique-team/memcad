// Ex list-18: allocation and deallocation of a list (procs)
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

void main( ){
  int a;
  list ll;
  ll = allocate( a );
  _memcad( "check_inductive( ll, list )" );
  deallocate( ll );
}
