// Ex prod-sep-05.c :
//    - an example with a large number of variables,
//      where separating conjunction would help
//    - an endless loop
//    - some operaration on numerical variables
//    - add/remove of an element of the list (on heap)
typedef struct list {
  struct list * next ;
  int data ;  
} list ;

void main( ){
  int x0 ;
  int x1 ;
  int x2 ;
  int x3 ;
  int x4 ;
  int x5 ;
  int x6 ;
  int x7 ;
  int x8 ;
  int x9 ;
  int x10 ;
  int x11 ;
  int x12 ;
  int x13 ;
  int x14 ;
  int x15 ;
  int x16 ;
  int x17 ;
  int x18 ;
  int x19 ;
  int x20 ;
  int x21 ;
  int x22 ;
  int x23 ;
  int x24 ;
  int x25 ;
  int x26 ;
  int x27 ;
  int x28 ;
  int x29 ;
  int x30 ;
  int x31 ;
  int x32 ;
  int x33 ;
  int x34 ;
  int x35 ;
  int x36 ;
  int x37 ;
  int x38 ;
  int x39 ;

  int y ;
  int z ;
  int t ;

  y = 0;
  z = 0;
  t = 0;
  volatile int rand;

  list* q ;
  list* q0;
  _memcad( "add_inductive( q, list )" );

  while( rand ){
    // take inputs
    x0 = rand ;  
    x1 = rand ;  
    x2 = rand ;  
    x3 = rand ;  
    x4 = rand ;  
    x5 = rand ;  
    x6 = rand ;  
    x7 = rand ;  
    x8 = rand ;  
    x9 = rand ;  
    x10 = rand ;  
    x11 = rand ;  
    x12 = rand ;  
    x13 = rand ;  
    x14 = rand ;  
    x15 = rand ;  
    x16 = rand ;  
    x17 = rand ;  
    x18 = rand ;  
    x19 = rand ;
    x20 = rand ;  
    x21 = rand ;  
    x22 = rand ;  
    x23 = rand ;  
    x24 = rand ;  
    x25 = rand ;  
    x26 = rand ;  
    x27 = rand ;  
    x28 = rand ;  
    x29 = rand ;  
    x30 = rand ;  
    x31 = rand ;  
    x32 = rand ;  
    x33 = rand ;  
    x34 = rand ;  
    x35 = rand ;  
    x36 = rand ;  
    x37 = rand ;  
    x38 = rand ;  
    x39 = rand ;   
    // complex numerical stuffs 
    y = x0 + x1 ;
    z = x1 + x2 + 3;
    y = z + y ; 
    y = x9 - x8 ;
    z = x6 - x7 ;
    z = y - z ;
    y = y - x3 ;
    z = y + x4 - 32;
    y = z * x5 ;
    y = x20 + x21 + y;
    z = x21 + x22 + z;
    y = z * y ; 
    y = x29 - x28 + 2 ;
    z = x26 - x27 ;
    z = y * z ;
    y = y - x23 ;
    z = y + x24 ;
    y = z * x25 ;
    y = x20 + x21 + y;
    z = x21 + x22 + z;
    y = z * y ; 
    y = x29 - x28 - 37 ;
    z = x26 * x27 ;
    z = y - z ;
    y = y - x23 ;
    z = y + x24 ;
    y = z - x35 ;
    y = x30 + x31 + y;
    z = x31 + x32 + z;
    y = z * y ; 
    y = x39 - x38 - 37 ;
    z = x36 * x37 ;
    z = y - z ;

    if( x39 > 0 ){ 
      t = 0; 
    }else{
      t = 1;
    }

    z = y + t ;
    y = y - t ;

    assert( z >= y );
    
    if( z > 0 ){
      // insert in q
      q0 = malloc( 8 ) ;
      if( q0 == 0 )
        exit( 0 );
      q0 -> next = q ;
      q0 -> data = y ;
      q = q0;
    }else{
      if( y > 0 && q != null ){
        // remove from q
        q0 = q;
        q = q -> next;
        free( q0 );
      }
    }
    _memcad( "check_inductive( q, list )" );
    //    q0 = null; // to help join
  }
  _memcad( "check_inductive( q, list )" );  
}
