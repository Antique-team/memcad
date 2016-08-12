// Ex submem-05: array used as a sub-memory + steps (main := sub) w/o unfold
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
  list m;
  list l;
  l = null;
  i = 0;
  m = &t[i];
  // note: it would break with the following instead...
  // k = &t[0];
  while( i < 10 ){
    t[i].next = l;
    t[i].data = 0;
    l = &t[i];
    i = i + 1;
  }
  _memcad( "force_live( l, t, i)" );
  _memcad( "check_inductive( l, list )" );
  assert( l != null ); // trivial: pointer into block
  assert( m != null ); // trivial: pointer into block
  if( m->data > 0 ){
    _memcad( "check_bottomness( true )" );
  } else {
    i = m->data;
    m = m->next;
    _memcad( "check_inductive( m, list )" );
    if( m != null ){ // should be unreachable
      m = m->next;
      _memcad( "check_inductive( m, list )" );
    }
  }
}
