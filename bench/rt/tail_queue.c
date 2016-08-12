// TOSORT
// tail queue example
#include <sys/queue.h>

TAILQ_HEAD(tailhead, entry) head;
struct tailhead *headp; /* Tail queue head. */
struct entry {
TAILQ_ENTRY(entry) entries; /* Tail queue. */
  int i;
} *n1, *n2, *n3, *np;

void main() {

  TAILQ_INIT(&head);                      /* Initialize the queue. */

  n1 = malloc(sizeof(struct entry));      /* Insert at the head. */
  n1->i = 1;
  TAILQ_INSERT_HEAD(&head, n1, entries);

  n2 = malloc(sizeof(struct entry));      /* Insert at the tail. */
  n2->i = 2;
  TAILQ_INSERT_TAIL(&head, n2, entries);

  n3 = malloc(sizeof(struct entry));      /* Insert after. */
  n3->i = 3;
  TAILQ_INSERT_AFTER(&head, n2, n3, entries);

#ifndef MEMCAD_INRIA
  for (np = head.tqh_first; np != NULL; np = np->entries.tqe_next) {
    printf("%d\n", np->i);
  }
#endif

  /* FBR: this loop crashes memcad */
  /* Delete. */
  while (head.tqh_first != NULL) {
    TAILQ_REMOVE(&head, head.tqh_first, entries);
  }
  free(n1);
  free(n2);
  free(n3);
}
