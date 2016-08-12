// prod-cart-02.c: random structure traversal,
//                 then read a data field and check structures
typedef struct idll {
  int id ;
  struct idll * next ;
  struct idll * prev ;
} idll ;

void main( ){

  int z ;
  idll* l ; 
  idll* nl ;
  // initialization  
  z = 42 ;
  nl = null ;  
  _memcad( "add_inductive( l, dll, [ nl | | ] )" ) ;
  _memcad( "add_inductive( l, ill, [ z | | ] )" ) ;  
  if( l != null ){
    // random traversal
    idll* ll ;
    volatile int rand ;
    ll = l ;
    while( rand ){
      if( ll -> next != null && rand ){
	ll = ll -> next; 
      }else{ 
	if( ll -> prev != null && rand ){
	  ll = ll -> prev ;
	}
      }
    }
    assert( ll != null );
    _memcad( "unfold( ll )" );
    assert( ll -> id == 42 );
  }
  // checks that structures are preserved
  _memcad( "check_inductive( l, ill, [ z | | ] )" ) ;
  _memcad( "check_inductive( l, dll, [ nl | | ] )" ) ;
}
