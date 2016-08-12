// Ex submem-04: array used as a sub-memory + ind_check
//  => simplified structure with no data field;
//     this should make the computation of segmentations easier
typedef struct elist {
  struct elist * next ;
} elist ;
typedef elist * list ;
void main( ){
  int i;
  elist t[10];
  list l;
  list k;
  l = null;
  i = 0;
  k = &t[i];
  // note: it would break with the following instead...
  // k = &t[0];
  while( i < 10 ){
    t[i].next = l;
    l = &t[i];
    i = i + 1;
  }
  assert( k->next == null );
  _memcad( "force_live( l, t, i)" );
  _memcad( "check_inductive( l, zlist )" );
}
