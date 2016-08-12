// Ex aplas-fpool-01: linking an array of cells inserting after tail
// Array version.
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  int i;
  list l;
  list fin;
  elist t[100];
  l = null;
  fin = null;
  i = 0;
  while( i < 100 ){
    t[i].next = &t[i]+1;
    i = i + 1;
  }
  t[99].next = null;
  l = &t[0]; 
  _memcad( "check_inductive( l, list )" );
  _memcad( "force_live(l, fin)" );
}
