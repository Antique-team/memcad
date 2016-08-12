// Ex c-micro-09: malloc, join
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
  k = 0;
  _memcad( "add_inductive( l, list )" );
  if( b ){
    m = l;
  } else {
    m = malloc( 8 );
    m->next = l;
    m->data = k;
  }
  assert( k <= 10 );
  _memcad( "check_inductive( l, list )" );
}
