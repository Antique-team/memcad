// Ex c-micro-10: malloc, join
// - malloc
// - join, with unfolding rule
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  list l;
  list m;
  int b;
  int k;
  k = 8;
  _memcad( "add_inductive( l, list )" );
  while( k >= 0 ){
    m = (list) malloc( sizeof( elist ) );
    m->next = l;
    m->data = k;
    l = m;
  }
  assert( k <= 0 );
}
