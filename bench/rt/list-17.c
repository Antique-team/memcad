// Ex list-17: allocation of a list (procs)
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

void main( ){
  int a;
  list l;
  l = allocate( a );
  _memcad( "check_inductive( l, list )" );
}
