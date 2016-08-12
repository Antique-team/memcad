// Ex submem-10: updates in the sub-memory,
//    of the form sub := sub
typedef struct elist {
  struct elist * next;
  struct elist * data;
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
    t[i].data = NULL;
    l = &t[i];
    i = i + 1;
  }
  _memcad( "check_inductive( l, list )" );
  if( l != null ){
    i = 20;
    l->data = l->data;
  }
  _memcad( "force_live( l, t, i)" );
}
