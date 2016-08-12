// Ex traversal.c: building then traversing a list
// Alloc version
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
  while( i < 10 ){
    elist *c;
    c = malloc( 8 );
    c->next = null;
    c->data = 99;
    if (fin != null) {
      fin->next = c;
      fin = fin->next;
    }
    else {
      l = c;
      fin = c;
    }
    i = i + 1;
  }
  list ln;
  ln = l;
  while( ln != fin) {
    ln = ln -> next;
  }
  assert(ln == fin);
  _memcad( "check_inductive( l, list )" );
}
