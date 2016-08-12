// Ex list-23: double list traversal, force_live command
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
  list ln;
  ln = l;
  while (ln->next != null) {
    ln = ln->next;
  }
  // issue with the guessing of segments ends
  _memcad( "force_live( k )" );
  _memcad( "check_inductive( l, list )" );
}
