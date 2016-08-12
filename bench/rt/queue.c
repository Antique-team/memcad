// TOSORT
// test the singly linked list provided by <sys/queue.h>
// some usage examples can be seen in QUEUE(3) from 'man queue'
#include <sys/queue.h>

struct entry {
  LIST_ENTRY(entry) entries; /* List. */
  int i;
} *n1, *n2, *n3, *np;

struct entry* new_entry(int n) {
  struct entry* res = malloc(sizeof(struct entry));
  res->i = n;
  return res;
}

LIST_HEAD(listhead, entry) head;

void main() {

  LIST_INIT(&head);

  n1 = new_entry(1);
  LIST_INSERT_HEAD(&head, n1, entries);

  n2 = new_entry(2);
  LIST_INSERT_AFTER(n1, n2, entries);

  n3 = new_entry(3);
  LIST_INSERT_AFTER(n2, n3, entries);

  /* FBR: this for loop crashes memcad */
  for (np = head.lh_first; np != NULL; np = np->entries.le_next) {
#ifndef MEMCAD_INRIA
    printf("%d\n", np->i);
#endif
  }

  /* FBR: this loop too crashes memcad */
  while (head.lh_first != NULL) { /* Delete all */
    LIST_REMOVE(head.lh_first, entries);
  }
  free(n1);
  free(n2);
  free(n3);
}
