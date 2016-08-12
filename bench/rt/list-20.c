// Ex list-20: allocation of a list (nested procs)
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
// list allocation function
list add_elt( list l ){
  list k;
  k = malloc( 8 );
  k->next = l;
  k->data = 0;
  return k;
}
list allocate( int n ){
  list m;
  int b;
  m = null;
  while( b < n ){
    m = add_elt( m );
  }
  return m;
}
void main( ){
  int a;
  list l;
  l = allocate( a );
  _memcad( "check_inductive( l, list )" );
}
