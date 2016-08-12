// EX c-micro-45: switch_to_if.c
// test switchToIf transformation

void reset(int* c1, int* c2, int* c3, int* d) {
  *c1 = -1;
  *c2 = -1;
  *c3 = -1;
  *d  = -1;
}

void main() {
  int c11, c1, c2, c3, d;
  int i;
  int j;

  c11 = -1;
  reset(&c1, &c2, &c3, &d);
  i = 1; // case 1 only
  j = 1;
  switch (i) {
  case 1:
    c1 = 1;
    switch (j) { // imbricated
      case 1:
        c11 = 1;
        break;
    }
    break;
  case 2:
    c2 = 2;
    break;
  case 3:
    c3 = 3;
    break;
  default:
    d = 4;
    break;
  }
  assert(c11 == 1 && c1 == 1 && c2 == -1 && c3 == -1 && d == -1);

  reset(&c1, &c2, &c3, &d);
  i = 4; // default only
  switch (i) {
  case 1:
    c1 = 1;
    break;
  case 2:
    c2 = 2;
    break;
  case 3:
    c3 = 3;
    break;
  default:
    d = 4;
    break;
  }
  assert(c1 == -1 && c2 == -1 && c3 == -1 && d == 4);

  reset(&c1, &c2, &c3, &d);
  i = 1; // case 1 to default
  switch (i) {
  case 1:
    c1 = 1;
  case 2:
    c2 = 2;
  case 3:
    c3 = 3;
  default:
    d = 4;
  }
  assert(c1 == 1 && c2 == 2 && c3 == 3 && d == 4);

  reset(&c1, &c2, &c3, &d);
  i = 3; // case 3 to default
  switch (i) {
  case 1:
    c1 = 1;
  case 2:
    c2 = 2;
  case 3:
    c3 = 3;
  default:
    d = 4;
  }
  assert(c1 == -1 && c2 == -1 && c3 == 3 && d == 4);

  reset(&c1, &c2, &c3, &d);
  i = 2; // case 2 and 3
  switch (i) {
  case 1:
    c1 = 1;
    break;
  case 2:
    c2 = 2;
  case 3:
    c3 = 3;
    break;
  default:
    d = 4;
  }
  assert(c1 == -1 && c2 == 2 && c3 == 3 && d == -1);

  reset(&c1, &c2, &c3, &d);
  i = 4; // default then case 1
  switch (i) {
  default:
    d = 4;
  case 1:
    c1 = 1;
    break;
  case 2:
    c2 = 2;
  case 3:
    c3 = 3;
    break;
  }
  assert(c1 == 1 && c2 == -1 && c3 == -1 && d == 4);

  reset(&c1, &c2, &c3, &d);
  i = 1; // all cases then default
  switch (i) {
  case 1:
  case 2:
  case 3:
  default:
    d = 4;
  }
  assert(c1 == -1 && c2 == -1 && c3 == -1 && d == 4);
}
