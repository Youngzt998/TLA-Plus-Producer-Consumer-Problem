### Producer & Consumer 问题建模



#### Problem_1: 含死锁

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



