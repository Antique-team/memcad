// Ex dll-11: dll random element removal
typedef struct edll {
  struct edll * next ;
  struct edll * prev ;
} edll ;
typedef edll * dll ;
volatile int cond;
void main( ){
  dll l ;
  dll p ;
  dll c ;
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  if( l != null ){
    c = l->next;
    while( c != null ){
      if( cond ){
        c = c->next;
      } else {
        dll m;
        m = c->next;
        if( m != null ){
          m->prev = c->prev;
        }
        if( c->prev != null ){
          c->prev->next = m;
        }
        free( c );
        c = m;
      }
      cond = cond;
    }
    _memcad( "check_bottomness( false )" );
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}


/* for selection merge test */
void main_e( ){
  dll l ;
  dll p ;
  dll c ;
  _memcad( "add_inductive( l, dllo, [ p | | ] )" );
  if( l != null ){
    c = l->next;
    while( c != null ){
      if( cond ){
        c = c->next;
      } else {
        dll m;
        m = c->next;
        if( m != null ){
          m->prev = c->prev;
        }
        if( c->prev != null ){
          c->prev->next = m;
        }
        free( c );
        c = m;
      }
      cond = cond;
    }
    _memcad( "check_bottomness( false )" );
    _memcad( "sel_merge(l, c, p)" );
  }
  _memcad( "check_inductive( l, dllo, [ p | | ] )" );
}
