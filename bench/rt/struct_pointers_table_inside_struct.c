
typedef struct node {
  struct node *sons[2];
} node_t;

void main() {
  node_t n;
  n.sons[0] = NULL;
  n.sons[1] = NULL;
  assert(n.sons[0] == NULL);
}
