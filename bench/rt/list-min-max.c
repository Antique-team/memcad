// Ex list-min-max: searching the minimum and maximum element 
// addresses
typedef struct elist {
  struct elist* next;
  int data;
} elist;

typedef elist* list;

void min_max(list h, list min, list max) {
  list c;
  _memcad("add_inductive(h, list)");
  min = max = c = h;
  while (c != NULL) {
    /* _memcad("output_dot(c,min,max, h | SUCC)"); */
    if (c->data < min->data)
      min = c;
    else if (c->data > max->data)
      max = c;
    c = c->next;
    /* _memcad("output_dot(c,min,max, h | SUCC)"); */
    _memcad("sel_merge()");
    /* _memcad("output_dot(c, min, max, h | SUCC)"); */
  }
  /* _memcad("output_dot(c, min, max, h | SUCC)"); */
  _memcad("check_inductive(h, list)");
}

void main() {
  list h, min, max;
  min_max(h, min, max);
}
