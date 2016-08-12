// -ex-01: experimenting with pointers around the liveness analysis

// Data-types
typedef struct Node {
  Node first;
  Node second;
  Node parent;
  Tree tree;
  int data;
} node;
typedef struct tree {
  Node root;
} tree;
typedef struct iterator {
  Tree tree;
  Node pointer;
} iterator;
typedef node* Node;
typedef tree* Tree;
typedef iterator* Iterator;

// Nodes
Node mkNode(Node f, Node s, Node p, Tree t, int d) {
  Node n;
  n = malloc( 20 );
  n->first = f;
  n->second = s;
  n->parent = p;
  n->tree = t;
  n->data = d;
  return n;
}

// Trees
Tree mkTree() {
  Tree t;
  t = malloc( 8 );
  t->root = NULL;
  return t;
}

// Iterators
Iterator iterator(Tree t) {
  Iterator i;
  i = malloc( 8 );
  i->tree = t;
  i->pointer = t->root;
  return i;
}

Node up(Iterator i) {
  return i->pointer->parent;
}

Node down(Iterator i) {
  if( i->pointer->first != NULL ){
    return i->pointer->first;
  } else {
    return i->pointer->second;
  }
}

Node left(Iterator i) {
  Node n;
  n = i->pointer;
  if( n->parent != NULL ){
    if( n->parent->first != n ){
      return n->parent->first;
    } else {
      return NULL;
    }
  } else {
    return NULL;
  }
}

Node right(Iterator i) {
  Node n;
  n = i->pointer;
  if( n->parent != NULL ){
    if( n->parent->second != n ){
      return n->parent->second;
    } else {
      return NULL;
    }
  } else {
    return NULL;
  }
}

int hasNext(Iterator i) { // return i->pointer != NULL;
  if( i->pointer != NULL ){
    return 1;
  } else {
    return 0;
  }
}

int current(Iterator i) {
  return i->pointer->data;
}

int next(Iterator i) {
  //  int ret = current(i);
  //  int going_up = 0;
  int ret;
  int going_up;
  ret = current(i);
  going_up = 0;
  Node temp;
  // Visiting on downward traversal.
  temp = down(i);
  if( temp != NULL ){
    // I have children, so go down.
    i->pointer = temp;
  } else {
    temp = right(i);
    if( temp != NULL ){
      // I don't have children, so I am done.  I have a sibling,
      // so go to my sibling.
      i->pointer = temp;
    } else {
      // I don't have children, so I am done.  I don't have
      // another sibling, so go back to my parent.
      i->pointer = up(i);
      going_up = 1;
    }
  }
  while( i->pointer != NULL && going_up ){
    // Revisiting on upward traversal.
    temp = right(i);
    if( temp != NULL ){
      i->pointer = temp;
      going_up = 0;
    } else {
      i->pointer = up(i);
    }
  }
  return ret;
}

// Test

// -a- main function that does just a node make
void main_a(){
  Node n0;
  Node n1;
  Node nr;
  Node nn;
  Tree tn;
  nn = NULL;
  tn = NULL;
  _memcad( "add_inductive( n0, node, [ nn, tn | | ] )" );
  _memcad( "add_inductive( n1, node, [ nn, tn | | ] )" );
  nr = mkNode( n0, n1, nn, tn, 0 );
  if( n0 != NULL ){
    n0->parent = nr;
  }
  if( n1 != NULL ){
    n1->parent = nr;
  }
  _memcad( "check_inductive( nr, node, [ nn, tn | | ] )" );
}

// -c- main function that assumes, and traverses completely
void main_c(){
  Node nn;
  Node n;
  Tree t;
  Iterator it;
  int i0;
  Node ptr;
  nn = NULL;
  t = mkTree();
  _memcad( "add_inductive( n, node, [ nn, t | | ] )" );
  t->root = n;
  it = iterator(t);
  i0 = hasNext(it);
  ptr = it->pointer;
  while( i0 ){
    i0 = next(it);
    i0 = hasNext(it);
    ptr = it->pointer;
    if( it->pointer == NULL ){
      break;
    }
  }
  _memcad( "force_live( ptr )" );
  // no real check to do on the iterator (the loop would just fail)
  // we check that the main structure is still there...
  _memcad( "check_inductive( n, node, [ nn, t | | ] )" );
}
