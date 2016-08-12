// Ex list-min-rec: searching the minimum element 
// addresses
typedef struct elist {
  struct elist* next;
  int data;
} elist;

typedef elist* list;

list min, min_pre;
list c, c_pre;

void min_search( ) {
  if (c == null)
    return;
  else if (c->data < min->data){
    min = c;
    min_pre = c_pre;
  }
  c_pre = c;
  c = c->next;
  /* _memcad( "sel_merge(min, min_pre, c, c_pre)" ); */
  /* _memcad( "output_dot(h, min, min_pre, c, c_pre | SUCC )" ); */
  min_search ();
}


void main() {
  list h;
  _memcad("add_inductive(h, list)");
  _memcad("assume(h != 0)");
  min = c_pre = h;
  min_pre = null;
  c = h->next;
  /* _memcad( "output_dot(h, min, min_pre, c, c_pre | SUCC )" ); */
  min_search();
  _memcad( "output_dot(h, min, min_pre, c, c_pre | SUCC )" );
  /* _memcad( "sel_merge()" ); */
  _memcad( "output_dot(h, min, min_pre, c, c_pre | SUCC )" );
 if(min_pre != null){
   min_pre->next = min->next;
   free(min);
 }
 else {
   h = h->next;
   free(min);
  }
  _memcad("check_inductive(h, list)");
}
