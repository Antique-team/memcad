#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>
#include <math.h>

typedef struct node {
  int name;
  struct node* next;
  struct edge* edges;
} node;

typedef struct edge {
  struct node* dest;
  struct edge* next;
} edge;

// a pseudo random int from [0; max_val]
int random_int(int max_val) {
  float ratio = (float)rand() / (float)RAND_MAX; // in [0; 1]
  return (roundf(ratio * max_val));
}

int count_outgoing_edges(node* n) {

  int res;

  if (n == NULL) {
    res = 0;
  } else {
    edge* current_edge = n->edges;

    for (res = 0 ; current_edge != NULL; ++res) {
      current_edge = current_edge->next;
    }
  }

  return res;
}

void partial_random_traverse(node* h) {

  if (h != NULL) {

    node* current_node = h;
    printf("node: %d\n", current_node->name);

    while (current_node != NULL) {

      int nb_edges = count_outgoing_edges(current_node);

      if (nb_edges <= 0) {
        current_node = NULL;
      } else {
        int chosen_edge = random_int(nb_edges - 1);
        edge* g = current_node->edges;

        int i;
        for (i = 0; i < chosen_edge ; ++i) {
          g = g->next;
        }
        current_node = g->dest;
        printf("node: %d\n", current_node->name);
      }
    }
  }
}

int main() {

  // setup graph from the paper
  // nodes
  node node0;
  node node1;
  node node2;
  node0.name = 0;
  node1.name = 1;
  node2.name = 2;
  node0.next = &node1;
  node1.next = &node2;
  node2.next = NULL;
  // edges
  edge edge01;
  edge edge02;
  edge edge21;
  edge01.dest = &node1;
  edge01.next = &edge02;
  edge02.dest = &node2;
  edge02.next = NULL;
  edge21.dest = &node1;
  edge21.next = NULL;
  node0.edges = &edge01;
  node1.edges = NULL;
  node2.edges = &edge21;

  // RNG setup
  struct timeval tv;
  gettimeofday(&tv, NULL);
  srand(tv.tv_usec);

  // do the job
  partial_random_traverse(&node0);

  return 0;
}
