// Ex submem-14: array used as a sub-memory + steps (main := sub)
//  => simplified structure with no data field;
//     this should make the computation of segmentations easier
typedef struct elist {
  struct elist * next;
  int data;
} elist ;
typedef elist * list ;
volatile int rand;
void main( ){
  int i;
  int cnt;
  elist t[10];
  list l;
  list k;
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
  k = l;
  cnt = 0;
  while( k != null && rand ){
    k = k->next;
    cnt = cnt + 1;
  }
  _memcad( "check_inductive( k, list )" );
  _memcad( "check_inductive( l, list )" );
  if( k == null ){
    _memcad( "check_bottomness( false )" );
  }
}

