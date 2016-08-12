// Ex submem-01: array used as a sub-memory,
//   but with no specific assertion to prove yet
// AKA sas-fpool-00
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  int i;
  elist t[100];
  list l;
  l = null;
  i = 0;
  while( i < 100 ){
    t[i].next = l;
    t[i].data = 0;
    l = &t[i];
    i = i + 1;
  }
  _memcad( "check_inductive( l, list )" );
}
