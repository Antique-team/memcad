// Ex tree-search-ele-rec.c
typedef struct etree {
  struct etree * l ;
  struct etree * r ;
  int data ;
} etree ;
typedef etree * tree ;

tree ele, ele_pre;
int data;

void search_ele (tree c, tree c_pre){
  if (c == null) return;
  else if (c->data == data){
    ele = c;
    ele_pre = c_pre;
    return;
  } 
  else if (c->data < data)
    search_ele (c->r, c);
  else search_ele(c->l, c);
}


void main( ){
  tree t;
  tree c, c_pre;
  ele_pre = null;
  ele = null;
  _memcad( "add_inductive( t, bintree_o )" );
  _memcad("assume(t != 0)");
  c = t;
  c_pre = null;
  search_ele(c, c_pre);
}
