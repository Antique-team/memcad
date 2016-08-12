// Ex tree-search-ele-rec.c
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int data ;
} etree ;
typedef etree * tree ;

tree ele, ele_pre;
int data;
tree c, c_pre;

void search_ele (){
  if (c == null) return;
  else if (c->data == data){
    ele = c;
    ele_pre = c_pre;
    return;
  } 
  else if (c->data < data)
    {
      c_pre = c;
      c = c->r;
    }
  else {
    c_pre = c;
    c = c->l;
  }
  /* _memcad( "output_dot(t, c, c_pre, ele, ele_pre | SUCC )" ); */
 search_ele();
}


void main( ){
  tree t;
  ele_pre = null;
  ele = null;
  _memcad( "add_inductive( t, bintree_o )" );
  _memcad("assume(t != 0)");
  c = t;
  c_pre = null;
  /* _memcad( "output_dot(t, c, c_pre, ele, ele_pre | SUCC )" ); */
  search_ele();
 _memcad( "sel_merge()" );
 /* _memcad( "output_dot(t, c, c_pre, ele, ele_pre | SUCC )" ); */
  _memcad( "check_inductive( t, bintree_o )" );
}
