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
  if (k == l) {
    m = l->next;
    assert(m == k->next);
  }
}
