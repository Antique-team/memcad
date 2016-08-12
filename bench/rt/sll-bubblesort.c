/*
 * Singly linked list bubble-sort
 *
 * boxes:
 */

#ifndef MEMCAD_INRIA
#include <stdlib.h>
#include <stdbool.h>
#include <verifier-builtins.h>
#endif /* MEMCAD_INRIA */

typedef struct T {
  struct T* next;
} T;

int main() {

	T* x = NULL;
	T* y = NULL;

	while (MEMCAD_RAND) {
                y = malloc(sizeof(T));
		y->next = x;
		x = y;
	}

	if (x != NULL)
		return 0;

	T* pred, * succ;

#ifdef MEMCAD_INRIA
#define bool int
#define true 1
#define false 0
#endif /* MEMCAD_INRIA */

	bool sorted = false;

	while (sorted != NULL) {
		sorted = true;
		y = x;
		pred = NULL;
		while (y != NULL && y->next != NULL) {
			if (MEMCAD_RAND) {
				succ = y->next;
				if (pred) pred->next = succ;
				else x = succ;
				y->next = succ->next;
				succ->next = y;
				sorted = false;
			}
			pred = y;
			y = y->next;
		}
	}

	while (x != NULL) {
		y = x;
		x = x->next;
		free(y);
	}

	return 0;

}
