# Parallel Programming 2

## Locks and Semaphores

### Locks or Semaphores
- Q: Why is the initial value of s significant?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/eaef8752-5fb0-4de3-a0b8-eca5c1ee6b90)

## Atomic Operations

### Implementation of Semaphores
- Q: What is a simple way to implement mutual exclusion?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/fbb8d51c-656b-46a6-ae72-bbc55dfe87b0)

### Multiple Consumers Example using the Test&Set Instruction
Thread acquires the lock and falls into the critical section.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/51fc705a-5779-45a1-80ca-a40f98ccea84)

If the process freezes inside the critical session, the processor will freeze.

### Nonblocking Synchronization
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/05ca4a16-20d1-4e55-9ead-18af59cf427f)

### Load-link & Store-conditional aka Load-reserve, Load-Locked
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e1a54c2d-a06a-44af-a1b0-3d40006c049a)

### Performance of Locks
- Q: Give examples of blocking atomic read-modify-write instructions and examples of non-blocking ones.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/17e24011-6d23-43ca-b09d-d3786367f1bf)

## Memory Fences

### Issues in Implementing Sequential Consistency
- Q: What are the 2 issues that complicate SC?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/08c2a19f-8abd-48ba-ad14-1f2fc9d78c42)

### Memory Fences - Instructions to sequentialize memory accesses
- Q: Give examples of the 3 relaxed memory models and what they mean.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/05522937-b932-432d-81e8-f144b33efa21)

- Explanation: Total Store Order: store followed by a load can be reordered

### Using Memory Fences
- Q: What instructions can be reordered?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1998dd35-675e-4e27-96c2-1a74601e5db2)

- A: Load Rhead and Load Rtail on the consumer side can be reordered. No other instructions (load/store) can be reordered due to memory fences and dependencies.

## Dekker's Algorithm

### Mutual Exclusion Using Load/Store
- Q: What is wrong with the code?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/77cc0aff-45c6-463d-90ec-4e5f40e81574)

- A: If the processes are interleaved, they can both set c1 and c2 to 1 and spin forever, causing deadlock.

### Mutual Exclusion: second attempt
- Q: What is livelock?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/cc8da97c-1851-4636-8968-e030e8a92f61)

- A: Livelock is a situation where 2 or more processes are constantly changing their state with response to the other ones without making any progress.

### A Protocol for Mutual Exclusion
- Q: Explain Dekker's algorithm.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e2142327-1a73-47a6-9fc9-a385f5abc3b1)

### Analysis of Dekker's Algorithm
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/4a084d67-9f33-4bcc-9cab-5c6c92d7a688)

### N-process Mutual Exclusion (Lamport's Bakery Algorithm)
- Q: Explain the algorithm.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ac62dfae-9af7-418d-b59b-a7747387c687)

- A: Process that wants to take the lock enters a queue. It waits until everyone before it has released the lock. When the turn comes, it grabs the lock and executes.
