// TOSORT
#include <sys/queue.h>

CIRCLEQ_HEAD(circleq, entry) head;
struct circleq *headp;              /* Circular queue head. */
struct entry {
  CIRCLEQ_ENTRY(entry) entries;   /* Circular queue. */
  int i;
} *n1, *n2, *n3, *n4, *np;

void main() {

  CIRCLEQ_INIT(&head);                /* Initialize the circular queue. */

  n1 = malloc(sizeof(struct entry));  /* Insert at the head. */
  n1->i = 1;
  CIRCLEQ_INSERT_HEAD(&head, n1, entries);

  n2 = malloc(sizeof(struct entry));  /* Insert at the tail. */
  n2->i = 2;
  CIRCLEQ_INSERT_TAIL(&head, n2, entries);

  n3 = malloc(sizeof(struct entry));  /* Insert after. */
  n3->i = 4;
  CIRCLEQ_INSERT_AFTER(&head, n2, n3, entries);

  n4 = malloc(sizeof(struct entry));  /* Insert before. */
  n4->i = 3;
  CIRCLEQ_INSERT_BEFORE(&head, n3, n4, entries);

  /* Forward traversal. */
  int j = 0;
  for (np = head.cqh_first; np != (void *)&head && j < 8; np = np->entries.cqe_next) {
#ifndef MEMCAD_INRIA
    printf ("%d\n", np->i);
#endif
    ++j;
  }

  /* Reverse traversal. */
  j = 0;
  for (np = head.cqh_last; np != (void *)&head && j < 8; np = np->entries.cqe_prev) {
#ifndef MEMCAD_INRIA
    printf ("%d\n", np->i);
#endif
    ++j;
  }

  /* Delete. */
  while (head.cqh_first != (void *)&head) {
    CIRCLEQ_REMOVE(&head, head.cqh_first, entries);
  }
  free(n1);
  free(n2);
  free(n3);
  free(n4);
}
