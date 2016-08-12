// Ex submem-07: updates of the for main := sub
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
    k = l->next;
    l->data = 24;
  }
  _memcad( "force_live( l, t, i)" );
}
