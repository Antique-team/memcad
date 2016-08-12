typedef struct elist {
  struct elist* next;
  int data;
} elist;

typedef elist* list;

void main() {
  list h;
  _memcad("add_inductive(h, list, [ | | ] )");
  list c, min, max, min_pre, max_pre, c_pre;
  if (h == NULL)
    return;
  min = max = c_pre = h;
  min_pre = max_pre = NULL;
  c = h -> next;
  // find min and max
  while (c != NULL) {
    /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
    if (c->data < min->data){
      min = c;
      min_pre = c_pre;
    } else if (c->data > max->data){
      max = c;
      max_pre = c_pre;
    }
    c_pre = c;
    c = c->next;
    /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
    _memcad("sel_merge()");
    /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  }
  /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  _memcad("sel_merge()");
  /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  // delete min and max
  if (min  == h && max == h) {
    // both at start of list
    h = h->next;
    free(min);
    /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  } else if (min == h && max != h) {
    // only min at start of list
    max_pre->next = max->next;
    h = h->next;
    free(min);
    free(max);
    /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  } else if (min != h && max == h) {
    // only max at start of list
    min_pre->next = min->next;
    h = h->next;
    free(min);
    free(max);
    /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  } else if (min == max_pre){
    // none at start of list
    min_pre->next = max->next;
    free(min);
    free(max);
    /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
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
    /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  }
  /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  _memcad("sel_merge()");
  /* _memcad("output_dot(h, c, min, max, min_pre, max_pre | SUCC)"); */
  _memcad("check_inductive(h, list, [ | | ] )");
  return;
}
