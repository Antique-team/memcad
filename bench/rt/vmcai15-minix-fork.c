// Ex Vmcai-minix-fork. The rewritten function of fork in Minix
struct mproc{
  int mflag;
  int mparent;
} mproc[24];

void main()
{
  int child;
  int index;
  int chindex;
  int proc_in_use;
  _memcad("minix_start");
  if (proc_in_use < 24){
    index = 3;
    while (index < 24) {
      if(mproc[index].mflag <= 0)
        break;
      index = index + 1;
    }
    mproc[index].mflag = 1;
    mproc[index].mparent = 2;
    proc_in_use = proc_in_use + 1;
    _memcad("minix_check");
  }
  return;
}
