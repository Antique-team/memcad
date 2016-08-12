// Ex submem-09: updates in the sub-memory,
//    of the form sub := cst
typedef struct elist {
  struct elist * next;
  int data;
} elist ;
typedef elist * list ;
void main( ){
  int i;
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
  _memcad( "check_inductive( l, list )" );
  if( l != null ){
    // this guard seems uneffective
    if( l->next != null ){
      l->next->data = 20;
      assert( l->next->data == 20 );
    }
  }
  _memcad( "force_live( l, t, i)" );
}
