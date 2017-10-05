// #include <assert.h>
// #include <malloc.h>
// #define _memcad(X)

// Data-types
typedef struct _node {
  struct _node * first;
  struct _node * second;
  struct _node * parent;
  struct _tree * tree;
  int data;
} node;

typedef struct _tree {
  struct _node * root;
  int iterators;
} tree;

typedef struct _iterator {
  struct _tree * tree;
  struct _node * pointer;
} iterator;

typedef node* Node;
typedef tree* Tree;
typedef iterator* Iterator;


// Nodes

Node mkNode(Node f, Node s, Node p, Tree t, int d) {
  Node n;
  n = malloc( sizeof(node) );
  if( n == 0 )
    exit( 0 );
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
  t = malloc( sizeof(tree) );
  if( t == 0 )
    exit( 0 );
  t->root = NULL;
  t->iterators = 0;
  return t;
}

void printNode(Node n, int indent) {
  if( n != NULL ){
    // printNode(n->second, indent + 3);
    // printf("%*s%d(%x)\n", indent, " ", n->data, (unsigned int)n);
    // printNode(n->first, indent + 3);
  }
}

void printTree(Tree t) {
  if( t != NULL ){
    printNode(t->root, 0);
  }
}

Node bstInsertNode(Tree t, Node n, int data) {
  if( n == NULL ){
    // return mkNode(NULL, NULL, NULL, t, data);
    Node n;
    n = mkNode(NULL, NULL, NULL, t, data);
    return n;
  } else {
    if( data < n->data ){
      n->first = bstInsertNode(t, n->first, data);
      n->first->parent = n;
    } else {
      n->second = bstInsertNode(t, n->second, data);
      n->second->parent = n;
    }
    return n;
  }
}

void bstInsertTree(Tree t, int data) {
  t->root = bstInsertNode(t, t->root, data);
}

// Iterators

Iterator mkIterator(Tree t) {
  Iterator i;
  i = malloc( sizeof(iterator) );
  if( i == 0 )
    exit( 0 );
  i->tree = t;
  i->pointer = t->root;
  t->iterators = t->iterators + 1;
  return i;
}

Node up(Iterator i) {
  return i->pointer->parent;
}

Node down(Iterator i) {
  // return i->pointer->first != NULL ? i->pointer->first : i->pointer->second;
  if( i->pointer->first != NULL ){
    return i->pointer->first;
  } else {
    return i->pointer->second;
  }
}

Node left(Iterator i) {
  //Node n = i->pointer;
  //return n->parent != NULL && n->parent->first != n ? n->parent->first : NULL;
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

int hasNext(Iterator i) {
  // return i->pointer != NULL;
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
    i->pointer = down(i);
  } else {
    temp = right(i);
    if( temp != NULL ){
      // I don't have children, so I am done.  I have a sibling,
      // so go to my sibling.
      i->pointer = right(i);
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
      i->pointer = right(i);
      going_up = 0;
    } else {
      i->pointer = up(i);
    }
  } 

  if( i->pointer == NULL ){
    // Finished the walk.
    i->tree->iterators = i->tree->iterators - 1;
  }

  return ret;
}

Node replace(Iterator dst_iter, Node src) {
  int itemp;
  itemp = hasNext(dst_iter);
  assert( itemp );
  assert(dst_iter->tree == src->tree);
  assert(dst_iter->tree->iterators == 1);

  Node dst;
  dst = dst_iter->pointer;

  src->parent = dst->parent;
  if( dst->parent->first == dst ){
    dst->parent->first = src;
  } else {
    dst->parent->second = src;
  }
  dst->parent = NULL;

  return dst;
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

// -b- main function that does init and checks the structure
//     will not work due to recursion in bstInsertTree
void main_b(){
  int i;
  volatile int v;
  Tree t;
  i = 0;
  t = mkTree();
  while( i < 100 ){
    bstInsertTree(t, v);
    i = i + 1;
  }
}

// -c- main function that assumes, and traverses completely
void main_c(){
  Node nn;
  Node n;
  Tree t;
  Iterator it;
  int i0;
  nn = NULL;
  t = mkTree();
  _memcad( "add_inductive( n, node, [ nn, t | | ] )" );
  t->root = n;
  it = mkIterator(t);
  i0 = hasNext(it);
  while( i0 ){
    i0 = next(it);
    i0 = hasNext(it);
  }
  // no real check to do on the iterator (the loop would just fail)
  // we check that the main structure is still there...
  _memcad( "check_inductive( n, node, [ nn, t | | ] )" );
}

// Todo:
//  - 
//  - main function that assumes, traverses up to random point and replaces


// Initial test functions

Tree mkTest() {
  //  int test[7] = { 4, 8, 2, 1, 3, 5, 7 };
  //  size_t i;
  Tree t;
  t = mkTree();
  // for( i = 0; i < 7; i++ ){
  //   bstInsertTree(t, test[i]);
  // }
  return t;
}

void test(Tree t, Node n, int at) {
  Iterator i;
  int itemp0;
  int itemp1;

  i = mkIterator(t);
  itemp0 = hasNext(i);
  while( itemp0 ){
    // printf("%d\n", next(i));
    itemp0 = next(i);
    itemp0 = hasNext(i);
  }

  i = mkIterator(t);
  itemp0 = hasNext(i);
  itemp1 = current(i);
  while( itemp0 && itemp1 != at ){
    next(i);
    itemp0 = hasNext(i);
    itemp1 = current(i);
  }

  itemp0 = hasNext(i);
  if( itemp0 ){
    replace(i, n);
  }
}

void main() {
  Tree t;
  Node n;
  t = mkTest();
  n = mkNode(NULL, NULL, NULL, t, 22);

  printTree(t);
  test(t, n, 3);
  printTree(t);
}
