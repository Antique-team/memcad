// Ex list-min-rec: searching the minimum and maximum element 
// addresses
typedef struct elist {
  struct elist* next;
  int data;
} elist;

typedef elist* list;

list min, min_pre, max, max_pre;
list c, c_pre;

void min_max_search() {
  if (c == null)
    return;
  else if (c->data < min->data)
    { min = c;
      min_pre = c_pre;
    }
  else if (c->data > max->data)
    { max = c;
      max_pre = c_pre;
    }
  c_pre = c;
  c = c->next;
  /* _memcad( "sel_merge()" ); */
  /* _memcad( "output_dot(h, min, min_pre, max, max_pre, c, c_pre | SUCC )" ); */
  min_max_search ();
 
}


void main() {
  list h;
  int i;
  _memcad("add_inductive(h, list)");
  _memcad("assume(h != 0)");
  min = max = c_pre = h;
  min_pre = max_pre = NULL;
  c = h->next;
 /* _memcad( "output_dot(h, min, max, c | SUCC )" ); */
  min_max_search();
  _memcad( "output_dot(h, min, max, c | SUCC )" );
  /* _memcad( "sel_merge()" ); */
  _memcad( "output_dot(h, min, max, c | SUCC )" );
  /* _memcad( "output_dot(h, min, min_pre, max, max_pre, c | SUCC )" ); */
  // delete min and max
  if (min_pre  == null && max_pre == null) {
    // both at start of list
    h = h->next;
    free(min);
    /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  } else if (min_pre == null && max_pre != null) {
    // only min at start of list
    max_pre->next = max->next;
    h = h->next;
    free(min);
    free(max);
  } else if (min_pre != null && max_pre == null) {
    // only max at start of list
    min_pre->next = min->next;
    h = h->next;
    free(min);
    free(max);
  } else if (min == max_pre){
    // none at start of list
    min_pre->next = max->next;
    free(min);
    free(max);
  } else if (max == min_pre ){
    max_pre->next = min->next;
    free(min);
    free(max);
  }
  else {
    min_pre->next = min->next;
    max_pre->next = max->next;
    free(min);
    free(max);
  }

  /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  _memcad("sel_merge()");
  /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  _memcad("check_inductive(h, list, [ | | ] )");
  return;

}
