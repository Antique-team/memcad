// Ex aplas-fpool-02: building then traversing a list
//                    (traversal.c)
// Array version
typedef struct elist {
  struct elist * next ;
  int data ;
} elist ;
typedef elist * list ;
void main( ){
  int i;
  list l;
  list fin;
  elist t[10];
  l = null;
  fin = null;
  i = 0;
  while( i < 10 ){
    t[i].next = null;
    t[i].data = 99;
    if (fin != null) {
      fin->next = &t[i];
      fin = fin->next;
    } else {
      l = &t[i];
      fin = &t[i];
    }
    i = i + 1;
  }
  list ln;
  ln = l;
  while( ln != fin ){
    ln = ln -> next;
  }
  assert(ln == fin);
  _memcad( "check_inductive( l, list )" );
}
