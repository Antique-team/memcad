// Ex list-min-rec: searching the minimum element 
// addresses
typedef struct elist {
  struct elist* next;
  int data;
} elist;

typedef elist* list;

list min, min_pre;

void min_search(list c, list c_pre ) {
  if (c == null)
    return;
  else if (c->data < min->data){
    min = c;
    min_pre = c_pre;
  }
  min_search (c->next, c);
}


void main() {
  list h, c, c_pre;
  _memcad("add_inductive(h, list)");
  _memcad("assume(h != 0)");
  min = c_pre = h;
  min_pre = null;
  c = h->next;
  min_search(c, c_pre);
}
