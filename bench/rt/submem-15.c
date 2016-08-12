// Ex submem-15: sub-memory example, with assertion on last
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
    t[i].data = 0;
    if( fin != null ){
      fin->next = &t[i];
      fin = fin->next;
    } else {
      l = &t[i];
      fin = &t[i];
    }
    i = i + 1;
  }
  list ln;
  ln = l -> next;
  assert( ln != null );
  _memcad( "check_inductive( l, list )" );
}
