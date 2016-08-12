// Ex submem-13: array used as a sub-memory + steps (main := sub)
//  => simplified structure with no data field;
//     this should make the computation of segmentations easier
typedef struct elist {
  struct elist * next;
  int data;
} elist ;
typedef elist * list ;
void main( ){
  int i;
  elist t[10];
  list l;
  l = null;
  i = 0;
  while( i < 10 ){
    t[i].next = l;
    t[i].data = 0;
    l = &t[i];
    i = i + 1;
  }
  _memcad( "force_live( l, t, i)" );
  _memcad( "check_inductive( l, list )" );
  assert( l != null ); // trivial: pointer into block
  if( l->data < 10 ){
    i = l->data;
    l = l->next;
    _memcad( "check_inductive( l, list )" );
    if( l != null ){
      l = l->next;
      _memcad( "check_inductive( l, list )" );
    }
  }
}

// At line 29, unable to read a cell.
// Lots of localization issues
// - the condition l != null does not seem to be taken into account.
// - indeed, it is performed at the main domain level, and not decomposed
//   into a sub-mem expression so that the internal node is never also
//   asserted non null
// - Also, the value of l at point 28 needs be checked...
