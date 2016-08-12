// Ex submem-06: array used as a sub-memory + steps (main := sub)
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
  if( l->data > 0 ){
    i = l->data;
    l = l->next;
    _memcad( "check_inductive( l, list )" );
    if( l != null ){
      l = l->next;
      _memcad( "check_inductive( l, list )" );
    }
  }
}
