// Ex submem-30: field + array used as a sub-memory,
//   but with no specific assertion to prove yet
// Issue: base offset, and stride
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
typedef struct tt {
  int f;
  elist t[10];
} tt;
void main( ){
  int i;
  // elist t[10];
  tt tt;
  list l;
  tt.f = 0;
  l = null;
  i = 0;
  while( i < 10 ){
    tt.t[i].next = l;
    tt.t[i].data = 0;
    l = &(tt.t[i]);
    i = i + 1;
  }
  _memcad( "force_live( l, tt, i)" );
}
