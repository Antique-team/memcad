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
    t[i].next = null;
    t[i].data = 0;
    if (fin != null) {
      fin->next = &t[i];
      fin = &t[i]; // fin->next;
    } else {
      l = &t[i];
      fin = &t[i];
    }
    i = i + 1;
  }
  _memcad( "check_inductive( l, list )" );
  _memcad( "force_live(l, fin)" );
}
