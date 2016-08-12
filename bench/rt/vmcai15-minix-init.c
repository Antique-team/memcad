// Ex Vmcai-minix-init. The rewritten function of init in Minix

struct mproc{
  int mflag;
  int mparent;
}mproc[24];
void main()
{
  int child;
  int index;
  int chindex;
  int proc_in_use;
  _memcad("minix_start");
  
      index = 23;
      mproc[index].mflag = 0;
      mproc[index].mparent = 0;
      index = 22;
      while (index >= 0 )    {
        mproc[index].mflag = 0;
        mproc[index].mparent = 0;
        index = index - 1; }
      index = 0;
      mproc[index].mflag = 1;
      mproc[index].mparent = 0;
      index = 1;
      mproc[index].mflag = 1;
      mproc[index].mparent = 0;
      index = 2;
      mproc[index].mflag = 1;
      mproc[index].mparent = 0;
      proc_in_use = 3;
      _memcad("minix_check");
    
  return;}
