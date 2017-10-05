// Ex flip_content.c: building then flipping two contents
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
  _memcad( "unroll(1)" );
  while( i < 10 ){
    elist *c;
    c = malloc( 8 );
    if( c == 0 )
      exit( 0 );
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

  // Identifying a first element
  list l1;
  int idx1;
  i = 0;
  l1 = l;
  while( i != idx1 && l1 != fin ) {
    l1 = l1 -> next;
    i = i + 1;
  }
  _memcad( "merge()" );

  // Identifying a first element
  list l2;
  int idx2;
  i = 0;
  l2 = l1;
  while( i != idx2 && l2 != fin ) {
    l2 = l2 -> next;
    i = i + 1;
  }
  _memcad( "merge()" );
  
  int tmp;
  tmp = l1->data;
  l2->data = l1->data;
  l1->data = tmp;

  _memcad( "force_live(l,l1,l2)" );
}
