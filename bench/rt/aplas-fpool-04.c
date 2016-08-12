typedef struct Cell {
  struct Cell *next;
  // int code;
  int prio;
} Cell;

void main() {
  int idx_free;
  Cell *deb;
  Cell *fin;
  Cell free_pool[10];
  deb = null;
  fin = null;
  idx_free = 0;
  _memcad( "unroll(1)" );
  while( idx_free < 10 ){
    int prio_panne;
    if (deb == null) {
      deb = &free_pool[idx_free];
      deb->next = null;
      deb->prio = prio_panne;
      fin = deb;
    } else {
      if (prio_panne < deb->prio) {
        // insertion en tete
        free_pool[idx_free].next = deb;
        free_pool[idx_free].prio = prio_panne;
        deb = &free_pool[idx_free];
      } else {
        if (prio_panne >= fin->prio) {
          // insertion en queue
          free_pool[idx_free].next = null;
          free_pool[idx_free].prio = prio_panne;
          fin->next = &free_pool[idx_free];
          fin = &free_pool[idx_free];
        } else {
          // insertion ordonnee
          Cell * cur;
          cur = deb;
          while(prio_panne >= cur->next->prio) {
            cur = cur->next;
            assert(cur != null);
          }
          free_pool[idx_free].next = cur->next;
          free_pool[idx_free].prio = prio_panne;
          cur->next = &free_pool[idx_free];
        }
      }
    }
    idx_free = idx_free + 1;
  }
  _memcad( "check_inductive( deb, list )" );
  _memcad( "force_live(deb, fin)" );
}
