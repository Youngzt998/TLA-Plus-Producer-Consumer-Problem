### Producer & Consumer 问题建模





#### Problem_1: 死锁和异常捕获

#### 1. 问题建模

###### 1.1. 状态设定

producer和consumer的代码如下，对每一个可能发生状态改变的命令前都设置一个状态参数，包括了

注释中的"Working", "Before-Sleeping", "After-Sleeping", "After-Changing", "Before-Wakeup",

其中由于insert_item() 和 remove_item()并没有具体含义，所以视作和改变count值一同作为一个原子操作(单独设一个状态效果相同)

- "Working"表示正在执行produce_item()或consume_item()
- "Before-Sleeping"表示判断完if语句为true，且准备进行sleep()语句
- "After-Sleeping"表示下一步会修改count的值
- "After-Changing"表示修改count值之后
- "Before-Wakeup"表示判断完if语句为true，且准备进行wakeup()语句

```C
void producer () {
    while (true) {
        /* W: Working */
        produce_item();
        if (count==N) /*BS: Before-Sleeping */
            sleep(); /*S: Sleeping" */
        /*AS: After-Sleeping */
        insert_item();
        count = count + 1;
        /*AC: After-Changing */
        if (count==1) /*BW: Before-Wakeup */
            wakeup(consumer);
}
```

```C
void consumer() {
    while(true) {
        if (count==0) /*BS: Before-Sleeping */
            sleep(); /*S: Sleeping" */
        /*AS: After-Sleeping */
        remove_item();
        count = count-1;
        /*AC: After-Changing */
        if (count == N - 1) /*BW: Before-Wakeup */
            wakeup(producer);
        /*W: Working */
        consume_item();
    }
}
```

在初始时，假设producer和consumer都处于“Working”状态

```
Init == 
    /\ Producer = "W"
    /\ Consumer = "W"
    /\ count = 0
```



###### 1.2. 状态转移

针对每一种可能到达的状态进行单独描述，然后将其合取起来，其中每一种状态转移仅仅表示一个producer或者consumer的单个状态的变化(wakeup指令除外)：

```TLA
Next ==
    \/ Producer_to_BS
    \/ Producer_to_S
    \/ Producer_to_AS
    \/ Producer_to_AC
    \/ Producer_to_BW
    \/ Producer_to_W
    \/ Consumer_to_BS
    \/ Consumer_to_S
    \/ Consumer_to_AS
    \/ Consumer_to_AC
    \/ Consumer_to_BW
    \/ Consumer_to_W
```

具体实现见代码 (Problem_1.tla)



###### 1.3. 异常与死锁

异常即为count > N 或者 count < 0; 死锁即为Producer 和 Consumer都处于 "S"状态，也可以使用TLA+运行时的Deadlock检测

```
Deadlock == 
    /\ Producer = "S"
    /\ Consumer = "S"
NoDeadlock ==
    ~ Deadlock
NoException1 == 
    count >= 0
NoException2==
    count <= N
```



#### 2. 运行情况

运行设定如下图：

寻找Deadlock时，把deadlock勾上；

寻找count<0时，把NoException1勾上；

寻找count>N时，把NoException2勾上



<img src="/home/youngster/Project/TLA-Plus-Producer-Consumer-Problem/Readme_ch.assets/image-20200618153244977.png" alt="image-20200618153244977" style="zoom:50%;" />





###### 2.1. 异常 (count < 0 或 count > N)

异常count < 0出现的情景为：

当consumer处于working状态时，producer插入item后把count设为1，然后准备执行唤醒操作（在if从句之后），此时consumer结束working，移走一个item并且把count减1即变为0，然后不断向下执行到sleep中，接着producer继续执行wakeup操作，consumer再次被唤醒，又将count减1变为-1，异常出现

异常count > N 的情景则与count<0完全对称



以下为设定N=2时模型运行捕获到一条异常count<0的运行截图：

<img src="/home/youngster/Project/TLA-Plus-Producer-Consumer-Problem/Readme_ch.assets/image-20200618152920220.png" alt="image-20200618152920220" style="zoom:50%;" />



其具体的异常路线如下(来自运行结果)

```
<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
 Consumer |-> "W",
 Producer |-> "W",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "Producer_to_AS",
   location |-> "line 42, col 8 to line 46, col 24 of module Problem_1"
 ],
 Consumer |-> "W",
 Producer |-> "AS",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 3,
   name |-> "Producer_to_AC",
   location |-> "line 55, col 5 to line 58, col 25 of module Problem_1"
 ],
 Consumer |-> "W",
 Producer |-> "AC",
 count |-> 1
],
[
 _TEAction |-> [
   position |-> 4,
   name |-> "Producer_to_BW",
   location |-> "line 61, col 5 to line 65, col 21 of module Problem_1"
 ],
 Consumer |-> "W",
 Producer |-> "BW",
 count |-> 1
],
[
 _TEAction |-> [
   position |-> 5,
   name |-> "Consumer_to_AS",
   location |-> "line 90, col 7 to line 94, col 23 of module Problem_1"
 ],
 Consumer |-> "AS",
 Producer |-> "BW",
 count |-> 1
],
[
 _TEAction |-> [
   position |-> 6,
   name |-> "Consumer_to_AC",
   location |-> "line 103, col 5 to line 106, col 25 of module Problem_1"
 ],
 Consumer |-> "AC",
 Producer |-> "BW",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 7,
   name |-> "Consumer_to_W",
   location |-> "line 117, col 5 to line 121, col 21 of module Problem_1"
 ],
 Consumer |-> "W",
 Producer |-> "BW",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 8,
   name |-> "Consumer_to_BS",
   location |-> "line 77, col 5 to line 81, col 21 of module Problem_1"
 ],
 Consumer |-> "BS",
 Producer |-> "BW",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 9,
   name |-> "Consumer_to_S",
   location |-> "line 84, col 5 to line 87, col 21 of module Problem_1"
 ],
 Consumer |-> "S",
 Producer |-> "BW",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 10,
   name |-> "Consumer_to_AS",
   location |-> "line 95, col 7 to line 100, col 23 of module Problem_1"
 ],
 Consumer |-> "AS",
 Producer |-> "W",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 11,
   name |-> "Consumer_to_AC",
   location |-> "line 103, col 5 to line 106, col 25 of module Problem_1"
 ],
 Consumer |-> "AC",
 Producer |-> "W",
 count |-> -1
]
>>
```



以下为捕获到的一条count > N = 2 的运行截图

![image-20200618154537657](/home/youngster/Project/TLA-Plus-Producer-Consumer-Problem/Readme_ch.assets/image-20200618154537657.png)

其路线与count<0的情况是完全对称的



###### 2.2. 死锁(Producer = Consumer = "S")

死锁发生的两种对称情景为：

- 某时刻count=0，consumer准备进入sleeping状态（if从句之后），接着producer不停运行到count=N，然后进入sleeping状态，接着consumer也进入sleeping状态

- 某时刻count=N，producer准备进入sleeping状态（if从句之后），接着consumer不停运行到count=0，然后进入sleeping状态，接着producer也进入sleeping状态

以下为捕获到死锁的运行截图

![image-20200618154755546](/home/youngster/Project/TLA-Plus-Producer-Consumer-Problem/Readme_ch.assets/image-20200618154755546.png)



以下为一个捕获到死锁的路线(对应了前一种情况)

```
<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
 Consumer |-> "W",
 Producer |-> "W",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "Consumer_to_BS",
   location |-> "line 102, col 5 to line 106, col 21 of module Problem_1"
 ],
 Consumer |-> "BS",
 Producer |-> "W",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 3,
   name |-> "Producer_to_AS",
   location |-> "line 67, col 8 to line 71, col 24 of module Problem_1"
 ],
 Consumer |-> "BS",
 Producer |-> "AS",
 count |-> 0
],
[
 _TEAction |-> [
   position |-> 4,
   name |-> "Producer_to_AC",
   location |-> "line 80, col 5 to line 83, col 25 of module Problem_1"
 ],
 Consumer |-> "BS",
 Producer |-> "AC",
 count |-> 1
],
[
 _TEAction |-> [
   position |-> 5,
   name |-> "Producer_to_BW",
   location |-> "line 86, col 5 to line 90, col 21 of module Problem_1"
 ],
 Consumer |-> "BS",
 Producer |-> "BW",
 count |-> 1
],
[
 _TEAction |-> [
   position |-> 6,
   name |-> "Consumer_to_AS",
   location |-> "line 120, col 7 to line 125, col 23 of module Problem_1"
 ],
 Consumer |-> "BS",
 Producer |-> "W",
 count |-> 1
],
[
 _TEAction |-> [
   position |-> 7,
   name |-> "Producer_to_AS",
   location |-> "line 67, col 8 to line 71, col 24 of module Problem_1"
 ],
 Consumer |-> "BS",
 Producer |-> "AS",
 count |-> 1
],
[
 _TEAction |-> [
   position |-> 8,
   name |-> "Producer_to_AC",
   location |-> "line 80, col 5 to line 83, col 25 of module Problem_1"
 ],
 Consumer |-> "BS",
 Producer |-> "AC",
 count |-> 2
],
[
 _TEAction |-> [
   position |-> 9,
   name |-> "Consumer_to_S",
   location |-> "line 109, col 5 to line 112, col 21 of module Problem_1"
 ],
 Consumer |-> "S",
 Producer |-> "AC",
 count |-> 2
],
[
 _TEAction |-> [
   position |-> 10,
   name |-> "Producer_to_W",
   location |-> "line 94, col 5 to line 98, col 21 of module Problem_1"
 ],
 Consumer |-> "S",
 Producer |-> "W",
 count |-> 2
],
[
 _TEAction |-> [
   position |-> 11,
   name |-> "Producer_to_BS",
   location |-> "line 54, col 5 to line 58, col 21 of module Problem_1"
 ],
 Consumer |-> "S",
 Producer |-> "BS",
 count |-> 2
],
[
 _TEAction |-> [
   position |-> 12,
   name |-> "Producer_to_S",
   location |-> "line 61, col 5 to line 64, col 21 of module Problem_1"
 ],
 Consumer |-> "S",
 Producer |-> "S",
 count |-> 2
]
>>
```





#### Problem_2: Semaphore

##### 1. 问题建模

###### 1.1. Semaphore

semaphore的原理参照以下代码:

```C
void down (semaphore &x) {
    if (x == 0)
        sleep_on(x);
    else 
        x.value = x.value - 1;
}

void up (semaphore &x) {
    if(sleep_num(x)>0)
        wake_up(x);
    else 
        x.value = x.value + 1;
}
```

根据semaphore的原理，一个down操作和一个up操作会造成两种不同的状态转换，所以对Semaphore的建模如下：

一个semaphore用一个record类型来表示，内容包含其值的大小(用value表示)和在此semaphore上休眠的线程的数量(用sleep表示);

down(&x)在TLA+中被分解为down(x)和sleep(x); up(&x)被分解为up(x)和wake(x)

- down(x)状态转换成功当且仅当当前x的值大于0； 如果x的值为0，则在x上休眠，即只能进行sleep(x)的状态转换；

- up(x) 状态转换成功当且仅当当前x上休眠线程的值为0；如果有线程在上面休眠，则会唤醒线程，即进行wake(x) 转换, 减去一个在休眠的线程

```TLA
(******************** down ********************)
down(x) ==
    \/ /\ x.value > 0
       /\ x' = [x EXCEPT !.value = x.value - 1]

sleep(x)==
    \/ /\ x.value = 0
       /\ x' = [x EXCEPT !.sleep = x.sleep + 1]


(********************* up *********************)
up(x) ==
    \/ /\ x.sleep = 0
       /\ x' = [x EXCEPT !.value = x.value + 1]
       
wake(x) ==
    \/ /\ x.sleep > 0
       /\ x' = [x EXCEPT !.sleep = x.sleep - 1]
```





###### 1.2. Consumer & Producer 

Consumer 和 Producer 的原理参照以下代码(produce/consumer/insert/remove已省略):

```C
semaphore mutex=1, empty=N, full=0;

void producer () {
    while (true) {
        /* U2: Up_2 */
        down(&empty); /* S1: Sleep_1 */
        	/* D1: Down_1 */
        	down(&mutex); /* S2: Sleep_2 */
        		/* D2: Down_2 */
        	up(&mutex); 
        	/* U1: Up_1 */
        up(&full);
        /* U2: Up_2 */
    }
}

void consumer() {
    while(true) {
        /* U2: Up_2 */
        down(&full); /* S1: Sleep_1 */
        	/* D1: Down_1 */
        	down(&mutex); /* S2: Sleep_2 */
        		/* D2: Down_2 */
        	up(&mutex); 
        	/* U1: Up_1 */
        up(&empty); 
        /* U2: Up_2 */
    }
}
```

上述代码的注释为两种线程的可能的状态，其中

- S1表示Producer线程正在empty上休眠/Consumer线程正在full上休眠

- S2表示Producer/Consumer线程正在mutex上休眠

- D1表示Producer结束down(&empty)后的状态[可能是将empty的值减一，也可能从休眠状态被唤醒]/

  Consumer结束down(&full)后的状态[可能是将full的值减一，也可能从休眠状态被唤醒]

- D2表示Producer/Consumer结束down(&mutex)后的状态[可能是将mutex的值减一，也可能从休眠状态被唤醒]

- U1表示Producer/Consumer结束up(&mutex)后的状态[可能是将mutex的值加一，也可能是唤醒mutex上的休眠线程]

- U2表示Producer结束up(&full)后的状态[可能是将full的值加一，也可能唤醒full上的休眠线程]/

  Consumer结束up(&empty)后的状态[可能是将empty的值加一，也可能唤醒empty上的休眠线程]



建模线程为一个record类型 [type, state], 其中 type \in  {"Producer", "Consumer"},  state \in {"U1", "U2", "S1", "S2", "D1", "D2"}

初始的时候，设定线程的状态都处于"U2"，即第一条语句执行之前，同时设定各个Semaphore的值:

```
Init ==
    /\ mutex = [value |-> 1, sleep |-> 0]
    /\ empty = [value |-> N, sleep |-> 0]
    /\ full = [value |-> 0, sleep |-> 0]
    /\ ProState = [x \in Producers |-> [type |-> "Producer", state |-> "U2"]]
    /\ ConState = [x \in Consumers |-> [type |-> "Consumer", state |-> "U2"]]
```



在程序运行过程中，每个线程都有8种可能的状态转换如下(从上到下):

```
 U1 --- U2
        |  \
        |   S1
        |  /
        D1 
        |  \
        |   S2
        |  /
        D2
        |
        U1 --- U2
```

在TLA+中可以表示为：

```TLA+
Next ==
    \E t \in Producers \cup Consumers:
        \/ U2_to_D1(t)
        \/ U2_to_S1(t)
        \/ S1_to_D1(t)
        \/ D1_to_D2(t)
        \/ D1_to_S2(t)
        \/ S2_to_D2(t)
        \/ D2_to_U1(t)
        \/ U1_to_U2(t)
```

每一种转换的具体实现详见代码以及注释;



在运行过程中，检查类型是否合法，以及三个semaphore的值是否正常:

```TLA+
\* Cardinality(S) == number of elements in set S
TypeOK == 
    /\ \A x \in threads: State(x).state \in StateTypes
    /\ \A x \in threads: State(x).type \in ThreadTypes
    /\ mutex.value \in 0..1
    /\ mutex.sleep \in 0..Cardinality(threads)
    /\ empty.value \in 0..N
    /\ empty.sleep \in 0..Cardinality(threads)
    /\ full.value \in 0..N
    /\ full.sleep \in 0..Cardinality(threads)
```

各个Semaphore上sleep线程的数量小于集合总数可以说明死锁没有出现；

在只有一个Producer和一个Consumer的时候，也可以定义NoDeadlock如下来表示死锁没有出现:

```
Deadlock ==
    \A x \in threads: State(x).state \in {"S1", "S2"}

NoDeadlock ==
    ~ Deadlock
```





##### 2. 模型运行

在TLA+ Toolbox中，设定初始值N=100, 且有三个Producer和三个Consumer

![image-20200619041132377](/home/youngster/Project/TLA-Plus-Producer-Consumer-Problem/Readme_ch.assets/image-20200619041132377.png)



同时设置Invariant为TypeOK和NoDeadlock [在多个Producer和Consumer的时候，NoDeadlock只能判断是否出现全局死锁，但不能用来证明是否有某两个线程相互局部死锁， 但在各只有一个线程的时候是可以作为证明的， 和运行过程中的死锁判断也等效]



最终性质检验的结果如下，没有出现异常和死锁

![image-20200619041751359](/home/youngster/Project/TLA-Plus-Producer-Consumer-Problem/Readme_ch.assets/image-20200619041751359.png)



