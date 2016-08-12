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
  elist t[10];
  l = null;
  fin = null;
  i = 0;
  _memcad( "unroll(1)" );
  while( i < 10 ){
    t[i].next = null;
    t[i].data = 99;
    if( fin != null ){
      fin->next = &t[i];
      fin = fin->next;
    } else {
      l = &t[i];
      fin = &t[i];
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

  tmp = idx1;
  tmp = idx2;
  tmp = 0;

  _memcad( "force_live(l,l1,l2)" );
}

// Issue at line 54
//  - localization problem
//  - it may be possible to reconstruct additional information
//  - best fix might be to try to preserve off_ds information after
//    a segment unfolding, using knowledge of the segment properties

// condition l2 != fin does not seem to be taken into account
