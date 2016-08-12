// Ex list-min-rec: searching the minimum and maximum element 
// addresses
typedef struct elist {
  struct elist* next;
  int data;
} elist;

typedef elist* list;

list min, max;

void min_search(list c) {
  if (c == null)
    return;
  else if (c->data < min->data)
    min = c;
  else if (c->data > max->data)
    max = c;
  
  min_search (c->next);
}


void main() {
  list h, c;
  _memcad("add_inductive(h, list)");
  _memcad("assume(h != 0)");
  min = max = h;
  c = h->next;
  min_search(c);
}
