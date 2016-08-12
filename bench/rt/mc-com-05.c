// Ex mc-com-05: MemCad reduce_eager command; for inductive-edge reduction reasoning
typedef struct idll {
  int* id ;
  struct idll * next ;
  struct idll * prev ;
} idll ;

void main( ){
  int* x ;
  x = malloc( 4 ) ;
  *x = 42 ;
  int z ;
  idll* l ; 
  idll* l0 ;
  // start init
  {
    idll* nl ;
    volatile int rand;

    nl = null ;  
    _memcad( "add_inductive( l, dll, [ nl | | ] )" ) ;
    _memcad( "add_inductive( l, ill, [ x | | ] )" ) ;
    l0 = l ;
    while( l != null && rand ){
      l = l -> next ;
    }
    _memcad( "merge()" ) ;
  }
  // end init
  if( l != null ){
    if( l->prev != null ){
      _memcad( "unfold_bseg( l )" ) ;
      _memcad( "reduce_eager( )" ) ;
      z = *( l -> prev -> id ) ;
      assert( z == 42 );
    }
  }
}
