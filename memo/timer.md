## Timer
调用setTimeout，创建了一个Timeout对象，将其插入到某个 **TimersList** 中。如果list不存在，则创建新的list并将其添加到 **timerListMap** 和 **timerListQueue(PriorityQueue)** 中. timerListMap 以定时器相对超时时间(格式化后的用户设置的timeout时间)为key. 

#### initialize timer handler
Node.js在初始化的时候设置了处理定时器的函数。(internal/bootstrap/node) 
```javascript
setupTimers(processImmediate, processTimers);
```
Node.js定时器模块在Libuv中只对应一个定时器节点。在Node.js初始化的时候，初始化了该节点。
```c++
void Environment::InitializeLibuv(bool start_profiler_idle_notifier) {  
    // 初始化定时器  
    CHECK_EQ(0, uv_timer_init(event_loop(), timer_handle()));  
    // 置unref状态
    uv_unref(reinterpret_cast<uv_handle_t*>(timer_handle()));  
}  
```
我们看到底层定时器节点默认是unref状态的，所以不会影响事件循环的退出。因为初始化时JS层没有定时节点。