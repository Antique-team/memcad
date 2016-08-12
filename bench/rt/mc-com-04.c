// Ex mc-com-04: MemCad reduce_eager command; for thin-edge reduction reasoning
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
  {
    idll* nl ;
    nl = null;  
    _memcad( "add_inductive( l, dll, [ nl | | ] )" );
    _memcad( "add_inductive( l, ill, [ x | | ] )" );
  }
  if( l != null ){
    if( l->next != null ){
      _memcad( "unfold( l->next )" ) ;
      _memcad( "reduce_eager( )" ) ;
      z = *( l -> next -> prev -> id ) ;
      assert( z == 42 );
    }
  }
}
