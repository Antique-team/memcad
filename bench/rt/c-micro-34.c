// EX c-micro-34: no_typedef_struct.c
/* test structs without typedef */

struct s {
  int i;
};

void f(struct s* toto, struct s* titi) {
  assert(toto->i == 5);
  assert(titi->i == 7);
}

/* void g(struct s toto) { */
/*   struct s titi = toto; */
/*   assert(titi.i == 5); */
/* } */

struct t {
  struct s u;
  struct t* prev;
  struct t* next;
};

struct v {
  int i;
} v[2];

void main() {
  struct s toto;
  struct s titi;
  toto.i = 5;
  titi.i = 7;
  f(&toto, &titi);
  /* FBR: Fri Sep 26 15:12:35 CEST 2014
     currently doesn't work in memcad */
  // g(toto);

  struct t tata;
  struct t tutu;
  tata.u.i = 5;
  tutu.u.i = 7;
  tata.next = &tutu;
  tutu.prev = &tata;

  assert(tutu.prev->u.i == 5);
  assert(tata.next->u.i == 7);

  v[0].i = 5;
  v[1].i = 7;

  assert(v[0].i == 5);
  assert(v[1].i == 7);
}
