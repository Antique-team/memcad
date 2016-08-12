// prod-cart-01.c: structure forward traversal,
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
  {
    // forward traversal
    idll* ll ;
    int zz ;
    volatile int rand ;
    ll = l ;
    while( ll != null && rand ){
      ll = ll -> next;       
    }
    if( ll != null){
      if( ll -> prev != null ){
	_memcad( "unfold_bseg( ll )" ) ;
	zz = ll -> prev -> id ;
	assert( zz == 42 );
      }
    }
  }
  // checks that structures are preserved
  _memcad( "check_inductive( l, ill, [ z | | ] )" ) ;
  _memcad( "check_inductive( l, dll, [ nl | | ] )" ) ;
}
