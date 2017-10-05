// Ex tree-stack.c

typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int data ;
} etree ;
typedef etree * tree ;

typedef struct elist {
  struct elist * n ;
  struct etree * d ;
} elist ;
typedef elist * list ;



list push(list top, tree t){
  list tmp = (list) malloc(sizeof (elist) );
  if (tmp == null) exit(0);
  else {
    tmp -> d = t;
    tmp -> n = top;
    top = tmp;
    return top;
  }
}

tree peek(list top){
  return top->d;
}

list pop(list top){
  list tmp = top;
  top = top -> n;
  free (tmp);
  return top;
}

list walk_down(tree root, int data){
  list s = null;
  tree c = root;
  _memcad( "add_inductive(s, stack, [ root, root| | ] )" );
  _memcad( "output_dot( root, c, s | SUCC )" );
  while (c!= null){
    _memcad( "output_dot( root, c, s | SUCC )" );
    s = push(s, c);
    if (c->data < data)
      c = c->r;
    else c = c->l;
    _memcad( "output_dot( root, c, s | SUCC )" );
  }
  return s;
}


void walk_up(list s){
  tree tmp;
  tree tmp1;
  int i;
  if (s == null) return;
  tmp = peek(s);
  s = pop(s);
  while (s!= null){
    tmp1 = peek(s);
    s = pop(s);
    if(tmp == tmp1 -> l)
      i = 0;
    else
      i = 1;
    tmp = tmp1;
  }
}



int main(){
  tree root;
  int data;
  _memcad( "add_inductive( root, tree, [ | | ] )" );
  _memcad("assume(root != 0)");
  list s = walk_down(root, data);
  walk_up(s);
  _memcad( "check_inductive( root, tree, [ | | ] )" );
  return 0;
  
}
