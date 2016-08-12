typedef unsigned int U32;


#define spoquelenth 16
#define sporenwunum 4

#define spodormant 1
#define spoready 2
#define sposuspend 3
#define Excuting 4
#define sponull 0
#define sponodeltask 1
#define spoidlerenwu sporenwunum+1
#define spoidlerenwu_id 0xa6

typedef struct {
    U32 id;
    U32 renwuhandler;
    U32 next;
    U32 used;
}sporenwuque;
sporenwuque sporenwuqlie[spoquelenth];
U32 spodormantq_tail = 15;
U32 sporeadyq_tail = 14;
U32 sposuspendq_tail = 13;
U32 spodormantq_head = 0;
U32 sporeadyq_head = 1;
U32 sposuspendq_head = 2;
void main()
{
    U32 cur,pre,next,node;
    _memcad("aos_start");
    node = 3;
    while(node < 13 ){
      if (sporenwuqlie[node].used == 0) {
        break;
      }
      node = node + 1;
    }
    if(node > 13){
      _memcad("minix_check");
    }
    else {
      if (sporenwuqlie[node].used > 0) {
        _memcad("minix_check");
      }
      else {
        cur = spodormantq_head;
        pre = spodormantq_head;
        next = sporenwuqlie[cur].next;
        sporenwuqlie[node].used = 1;
        sporenwuqlie[pre].next = node;
        sporenwuqlie[node].next = next;
        _memcad("minix_check");
      }
    }
    return ;
}
