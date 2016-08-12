// TOSORT

struct _node {
  int i;
};
/* /\* FBR: version that works *\/ */
/* typedef struct _node { */
/*   int i; */
/* } _node; */

typedef struct _node* node_t;
/* /\* FBR: version that works *\/ */
/* typedef _node* node_t; */

void main() {

  node_t x;

  if (x == 0)
    ;

}
