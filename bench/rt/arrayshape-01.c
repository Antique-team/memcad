
#define NUM_TASKS  128
#define NO_TASK  255

int m_head;
int m_tail;
int m_next[NUM_TASKS];

int main ()
{
  
  _memcad( "add_segment( m_next[m_head], alist,[ |m_tail| ] *= m_next[m_tail], atail )");
  if( m_head != NO_TASK )
    {
      int id = m_head;
      m_head = m_next[m_head];
      if( m_head == NO_TASK )
        {
          m_tail = NO_TASK;
        }
      m_next[id] = NO_TASK;
   _memcad( "check_segment( m_next[m_head], alist,[ |m_tail| ] *= m_next[m_tail], atail )");
      return id;
    }
  else
    {
      return NO_TASK;
    }
}
