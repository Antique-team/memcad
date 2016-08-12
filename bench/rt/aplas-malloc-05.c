typedef struct Cell {
  struct Cell *next;
  // int code;
  int prio;
} Cell;

void main() {
  int idx_free;
  Cell *deb;
  Cell *fin;
  while(1) {
  deb = null;
  fin = null;
  idx_free = 0;
  _memcad( "unroll(1)" );
  while(idx_free < 10) {
    int prio_panne;
    Cell *free_cell;
    free_cell = malloc( 8 );
    if (deb == null) {
      deb = free_cell;
      deb->next = null;
      deb->prio = prio_panne;
      fin = deb;
    }
    else {
      if (prio_panne < deb->prio) {
	// insertion en tete
	free_cell->next = deb;
      	free_cell->prio = prio_panne;
      	deb = free_cell;
      } else {
	if (prio_panne >= fin->prio) {
	  // insertion en queue
	  free_cell->next = null;
	  free_cell->prio = prio_panne;
	  fin->next = free_cell;
	  fin = free_cell;
	} else {
	  // insertion ordonnee
	  Cell * cur;
	  cur = deb;
	  while(prio_panne >= cur->next->prio) {
	    cur = cur->next;
	    assert(cur != null);
	  }
	  free_cell->next = cur->next;
	  free_cell->prio = prio_panne;
	  cur->next = free_cell;
	  cur = null;
	}
      }
    }
    idx_free = idx_free + 1;
  }
  _memcad( "check_inductive( deb, list )" );
  _memcad( "merge()" );
  while(deb != fin) {
    Cell *hd;
    hd = deb;
    deb = hd->next;
    free(hd);
  }
  free(fin);
  _memcad( "merge()" );
  _memcad( "force_live(deb, fin)" );
  }
}
