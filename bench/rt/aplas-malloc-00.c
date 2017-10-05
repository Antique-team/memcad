// Ex head_alloc.c : linking an array of cells inserting before head
// Alloc version
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
  while( i < 100 ){
    elist *c;
    c = malloc( 8 );
    if( c == 0 )
      exit( 0 );
    c->next = l;
    c->data = 0;
    l = c;
    i = i + 1;
  }
  _memcad( "check_inductive( l, list )" );
}
