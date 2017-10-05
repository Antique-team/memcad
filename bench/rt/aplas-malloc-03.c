// Ex random_alloc.c : linking an array of cells inserting at random
// Alloc version.
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  int i;
  list l;
  l = null;
  i = 0;
  _memcad( "unroll(1)" );
  while( i < 10 ){
    elist *c;
    c = malloc ( 8 );
    if( c == 0 )
      exit( 0 );
    c->data = 0;
    if (l != null) {
      elist *tmp;
      tmp = l;
      int b;
      while(tmp->next != null) {
	tmp = tmp->next;
      }
      c->next=tmp->next;
      tmp->next = c;
    } else {
      l = c;
      c->next = null;
    }
    i = i + 1;
  }
  _memcad( "check_inductive( l, list )" );
}
