// Ex submem-00: array used as a sub-memory,
//   but with no specific assertion to prove yet
typedef struct elist {
  struct elist * next ;
  int data ;
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
    //t[i].data = 0;
    l = &t[i];
    i = i + 1;
  }
  _memcad( "force_live( l, t, i)" );
}
