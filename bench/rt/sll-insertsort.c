// list insert sort
typedef struct elist {
  struct elist * n ;
  int d ;
} elist ;
typedef elist * list ;

int main(){
  list x;
  list y = null;
  _memcad( "decl_setvars( F )" );
  _memcad( "add_inductive(x, lists, [ | | F ] )" );
  list sorted = null;
  list pred = null;
  list z = null;
  while (x!=null){
    _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
    y = x;
    x = x->n;
    pred = null;
    z = sorted;

    while(z!= null){
      _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
      if( z->d < y->d){
	pred = z;
	z = z->n;
      }
      else break;
      _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
    }
    y->n = z;
    if (pred != null) pred->n =y;
    else sorted = y;
    _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
  }
  _memcad( "check_inductive(sorted, lists, [ | | F])" );
  return 0;
}

int main_a(){
  list x;
  list y = null;
  int len;
  int len1 = 0;
  len = len + len1;
  int n;
  _memcad( "add_inductive(x, lenlist, [ | len| ] )" );
  list sorted = null;
  _memcad( "add_inductive(sorted, sortlist, [ |n, len1| ] )" );
  list pred = null;
  list z = null;
  while (x!=null){
    _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
    y = x;
    x = x->n;
    pred = null;
    z = sorted;
    while(z!= null){
      _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
      if( z->d < y->d){
	pred = z;
	z = z->n;
      }
      else break;
      _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
    }
    y->n = z;
    if (pred != null) pred->n =y;
    else sorted = y;
    _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
  }
  /* _memcad( "check_inductive(sorted, sortlist, [ | | ])" ); */
  return 0;
}

int main_b(){
  list x;
  int n;
  int len;
  int len1 = 0;
  len = len + len1;
  _memcad( "add_inductive(x, sortlist, [ |n, len| ] )" );
  _memcad("assume(x != 0)");
  list y = x;
  int b;
  if (b) y = x->n;
  _memcad( "merge()" ) ;
  return 0;
}


int main_c(){
  list x;
  int len;
  int len1 = 0;
  len = len + len1;
  _memcad( "add_inductive(x, lenlist, [ | len| ] )" );
  _memcad("assume(x != 0)");
  list y = x;
  int b;
  if (b) y = x->n;
  _memcad( "merge()" ) ;
  return 0;
}


int main_d(){
  list x;
  list y = null;
  int len;
  int len1 = 0;
  len = len + len1;
  int n;
  _memcad( "add_inductive(x, lenlist, [ | len| ] )" );
  list sorted = null;
  _memcad( "add_inductive(sorted, sortlist, [ |n, len1| ] )" );
  list pred = null;
  list z = null;
  while (x!=null){
    _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
    y = x;
    x = x->n;
    pred = null;
    z = sorted;
    while(z!= null){
      _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
      if( z->d < y->d){
	pred = z;
	z = z->n;
      }
      else break;
      _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
    }
    /* sel_merge fails because joining an empty inductive edge with
       a non-empty inductive edge, this will cause precision lose */
    _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
    _memcad( "sel_merge()" );
    _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
    y->n = z;
    if (pred != null) pred->n =y;
    else sorted = y;
    _memcad( "output_dot(x,y, sorted, pred, z | SUCC )" );
  }
  /* _memcad( "check_inductive(sorted, sortlist, [ | | ])" ); */
  return 0;
}
