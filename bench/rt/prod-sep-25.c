// Ex prod-sep-25.c :
//    - an example with a large number of variables,
//      where separating conjunction would help
//    - some operaration on numerical variables
//    - some memory allocation on heap
typedef struct list {
  struct list * n ;
  int id ;  
} list ;
typedef struct tree {
  struct tree * l ;
  struct tree * r ;
  int d ;  
} tree ;

void main( ){

  int i0 ;
  int i1 ;
  int i2 ;
  int i3 ;
  int i4 ;
  int i5 ;
  int i6 ;
  int i7 ;
  int i8 ;
  int i9 ;
  int i10 ;
  int i11 ;
  int i12 ;
  int i13 ;
  int i14 ;
  int i15 ;
  int i16 ;
  int i17 ;
  int i18 ;
  int i19 ;
  int i20 ;
  int i21 ;
  int i22 ;
  int i23 ;
  int i24 ;
  int i25 ;
  int i26 ;
  int i27 ;
  int i28 ;
  int i29 ;
  int i30 ;
  int i31 ;
  int i32 ;
  int i33 ;
  int i34 ;
  int i35 ;
  int i36 ;
  int i37 ;
  int i38 ;
  int i39 ;
  int i40 ;
  int i41 ;
  int i42 ;
  int i43 ;
  int i44 ;
  int i45 ;
  int i46 ;
  int i47 ;
  int i48 ;
  int i49 ;

  list* l0 ;
  list* l1 ;
  list* l2 ;

  tree* t0 ;
  tree* t1 ;
  tree* t2 ;

  volatile int rand;

  _memcad( "add_inductive( l0, list )" );
  l1 = null;
  l2 = null;
  _memcad( "add_inductive( t0, bintree_o )" );
  t1 = null;
  t2 = null;

  while( rand ){
    _memcad( "check_inductive( l0, list )" );
    _memcad( "check_inductive( t0, bintree_o )" );    
    i0 = rand;
    i10 = rand;
    i20 = rand;
    i30 = rand; 
    i40 = rand;
    // num 
    i1 = i1 + i0;
    i2 = i3;
    i4 = i2;
    i3 = i2 * i5;
    i7 = i42 - i14;
    i49 = 3 * i23 - 666;
    i30 = i30 + 1;
    if( i49 + 1 <= i30 ){
      i31 = i31 + 1;
    }else{
      i31 = i31 - 1;
    }
    // list stuff
    if( i31 > 0 ){
      i0 = i23;
    }else{
      i0 = i37;
    }
    // search for i0 in l0
    l1 = l0;
    while( l1 != null && rand ){
      l1 = l1 -> n;
    }
    // search for i10 in t0
    t1 = t0;
    while( t1 != null && rand ){
      i1 = t1 -> d;
      if( i1 > i25 ){
        t1 = t1 -> l;
      }else{
        t1 = t1 -> r;
      }
    }
    // end of loop
    l1 = null;
    l2 = null;
    t1 = null;
    t2 = null;
  }
  _memcad( "check_inductive( l0, list )" );
  _memcad( "check_inductive( t0, bintree_o )" );
}
