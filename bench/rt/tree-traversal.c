// Ex tree-traveral.c

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


int main(){
  tree root;
  tree tmp;
  int data;
  _memcad( "decl_setvars( E, F )" );
  _memcad ("set_assume ( F = $empty)");
  _memcad( "add_inductive( root, tree, [ | | E ] )" );
  _memcad("assume(root != 0)");
  list s = null;
  _memcad( "add_inductive(s, stack, [ | | F ] )" );
  s = push(s, root) ;
  while(s != null){
    tmp = peek(s);
    s = pop(s);
    if (tmp->l != null)
      s = push(s, tmp->l);
    if (tmp->r != null)
      s = push(s, tmp->r);
    _memcad( "output_dot( root, tmp, s | SUCC )" );
  }
  _memcad( "check_inductive( root, tree, [ | | ] )" );
  return 0;
  
}

/* list search */
int main_a(){
  list s;
  _memcad( "decl_setvars( F )" );
  _memcad( "add_inductive(s, stack, [ | | F ] )" );
  list tmp = s;
  while(tmp != null){
    tmp = tmp -> n;
    _memcad( "output_dot(tmp, s | SUCC )" );
  }
  _memcad( "check_inductive(s, stack, [ | | F] )" );
  return 0;
  
}

/* tree search */
int main_b(){
  tree s;
  _memcad( "decl_setvars( F )" );
  _memcad( "add_inductive(s, tree, [ | | F ] )" );
  tree tmp = s;
  while(tmp != null){
    int b;
    if (b)
      tmp = tmp -> l;
    else
      tmp = tmp -> r;
    _memcad( "output_dot(tmp, s | SUCC )" );
  }
  _memcad( "check_inductive(s, tree, [ | | F] )" );
  return 0;
  
}

/* list reverse */
int main_c(){
  list s;
  _memcad( "decl_setvars( F )" );
  _memcad( "add_inductive(s, stack, [ | | F ] )" );
  _memcad( "assume(s != 0)");
  list c = s;
  s = null;
  while(c != null){
    list tmp = c->n;
    c->n = s;
    s = c;
    c = tmp;
    _memcad( "output_dot(tmp, s, c, t| SUCC )" );
  }
  _memcad( "check_inductive(s, stack, [ | | F] )" );
  return 0;
  
}

/* list insert sort */
int main_d(){
  list x;
  list y = null;
  _memcad( "decl_setvars( F )" );
  _memcad( "add_inductive(x, stack, [ | | F ] )" );
  list sorted = null;
  list pred = null;
  list z = null;
  while (x!=null){
    y = x;
    x = x->n;
    pred = null;
    z = sorted;

    while(z!= null && z->d < y->d){
      pred = z;
      z = z->n;
    }
    y->n = z;
    if (pred != null) pred->n =y;
    else sorted = y;
  }
  _memcad( "check_inductive(sorted, sll)" );
  return 0;
  
}

