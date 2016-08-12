// Ex submem-02: array used as a sub-memory,
//   but with no specific assertion to prove yet
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
  l = null;
  i = 0;
  while( i < 10 ){
    t[i].next = l;
    l = &t[i];
    i = i + 1;
  }
  _memcad( "force_live( l, t, i)" );
}
