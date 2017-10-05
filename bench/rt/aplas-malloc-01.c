// Ex tail_alloc.c : linking an array of cells inserting after tail
// Alloc version.
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  int i;
  list l;
  list fin;
  l = null;
  fin = null;
  i = 0;
  while( i < 100 ){
    elist *c;
    c = malloc ( 8 );
    if( c == 0 )
      exit( 0 );
    c->next = null;
    c->data = 0;
    if (fin != null) {
      fin->next = c;
      fin = c;
    }
    else {
      l = c;
      fin = c;
    }
    i = i + 1;
  }
  _memcad( "check_inductive( l, list )" );
  _memcad( "force_live(l, fin)" );
}
