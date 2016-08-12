// Ex Vmcai-minix-exit. The rewritten function of exit in Minix
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
  if( child < 24 )
    if( child > 2 )
      if( mproc[child].mflag > 0){
        index = 0;
        proc_in_use = proc_in_use - 1;
        mproc[child].mflag = 0;
        if( mproc[index].mflag > 0 ){
          if( mproc[index].mparent == child ){
            mproc[index].mparent = 2;
          }
        }
        index = index + 1;
        while( index < 24 ){
          if( mproc[index].mflag > 0 ){
            if( mproc[index].mparent == child ){
              mproc[index].mparent = 2;
            }
          }
          index = index + 1;
        }
        _memcad( "minix_check" );
      }
  return;
}
