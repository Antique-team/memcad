
/* since memcad doesn't know about function pointers, we specialize all */
/* GDSL data structures to manipulate dynamically allocated integers */

#include "gdsl_types.h"

typedef int* gdsl_element_t;

static gdsl_element_t alloc_func (int* e)
{
  int* res = (int*) malloc (sizeof(int));
  *res = *e;
  return res;
}

static void free_func (gdsl_element_t e)
{
  free(e);
}

static int comp_f(const int* e1, const int* e2)
{
  return (*e1 - *e2);
}

// does nothing
static int map_f(gdsl_element_t e, gdsl_location_t l, void* user_data) {
  return GDSL_MAP_CONT;
}

void write_f (gdsl_element_t e, FILE* f, void* user_data) {
  fprintf(f, "%d\n", *e);
}
