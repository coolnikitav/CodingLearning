# Parallel Programming 1

## SMT Implementation

### Changes in Power 5 to support SMT
- Q: How was Power 5 changed to support SMT?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8f69976e-cee8-4324-9338-e0457df736eb)

### Pentium-4 Hyperthreading
- Q: What is hyperthreading?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/83ce8136-2ad5-4eb9-8f14-3839526dfa8e)

### Initial Performance of SMT
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/60960ae1-b4f2-4c48-be53-d4c5c1df8b6d)

### Icount Choosing Policy
- Q: what is the Icount choosing policy?
  
You want to fill holes in one thread with work from another thread.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/29148ca2-8080-4ad0-9b71-209ccc599ffa)

## Introduction to Parallelism

### Trends in Computation
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e7ba5f39-09ac-42b5-9989-ed5f89e86920)

### Symmetric Multiprocessors
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/10dd8b1b-d980-4dea-8047-2e040279a076)

### Synchronization
- Q1: Explain the producer-consumer and mutual exclusion models.
- Q2: How can you have synchronization issues on a uniprocessor system?

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/797c7a7b-33b8-4433-b7f9-ea395a908ef8)

- A2: You can have different entities: disk drive, caches, etc... trying to access the same locations.
  
### A Producer-Consumer Example
- Q1: Why does the consumer check Rhead == Rtail?
- Q2: What potential problem does this system have?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2be02385-6ec7-4855-9f9f-600d043e3b97)

- A1: If they are equal, then queue is empty. So it will spin until new data is added.
- A2: This only works if instructions are executed in order. What about OOO processors?

### A Producer-Consumer Example continued
- Q: Can we assume that if 3 happens after 2, then 4 happens after 1? Why or why not?

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/68378dcc-cd9e-4a30-ac26-9af86a29b06e)

- A: Loads and stores can have some dependencies. However, an OOO processor can reorder stores and loads however it needs.

## Sequential Consistency

### Sequential Consistency - A Memory Model
- Q: Explain sequential consistency
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/163380d3-fcdc-49ed-984a-4bda6175c256)

### Blackboard Example: Sequential Consistency
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f79a7103-5e7f-4b63-bc07-b9a36164e506)

- Q: Why is sequential consistency almost never implemented in real processors?
- A: Reordering Loads and Stores is good for performance because it can hide latency

### Sequential Consistency
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b5e304a4-73d1-4690-96e7-51bf449e6806)

The only way to get {0,11} is to execute non-sequentially: swap the stores in T1.

### Sequential Consistency
- Q: Does (can) a system with caches or out-of-order execution capability provide a sequentially consistent view of the memory?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d1e6353e-cf43-466f-bc59-0b07310d4929)

- A: Probably not.

## Introduction to Locks

### Multiple Consumer Example
- Q: What is the issue with the code?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c3c5a532-1b9d-455d-8c63-fd03a9c086e4)

- A: Both consumers will read the same value from the queue.

### Locks or Semaphores
- Q: Explain what a lock and semaphore is.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/6845d0e1-dc42-4a2a-a22b-0c7f24097894)

Semaphore helps when you want for example 2 out of the 3 processing using a resource. A single user lock would not work in this situation.
