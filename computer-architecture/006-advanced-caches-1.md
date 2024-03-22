# Advanced Caches 1
## Basic Cache Optimizations
### Average Memory Acccess Time 
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/59ca2378-d020-4912-a85b-352261c83be4)

- Average Memory Access Time = Hit Time + (Miss Rate * Miss Penalty)

### Categorizing Misses: The Three C's
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/fe7db262-835b-4307-b384-d3543ec18d22)

- Compulsory - first-reference to a block, occur even with infinite cach
- Capacity - cache is too small to hold all data needed by program, occur even under perfect replacement policy (loop over 5 cache lines)
- Conflict - misses that occur because of collisions due to less than full associativity (loop over 3 cache lines)

### Reduce Hit Time: Small & Simple Caches
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c4b5003d-1de4-4a2e-a52a-d6aa04275b6c)

### Reduce Miss Rate: Large Block Size
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/9176dd33-db6e-4cb3-a6fa-81580afa7918)

- Less tag overhead
- Exploit fast burst transfers from DRAM
- Exploit fast burst transfers over wide on-chip busses
- Can waste bandwidth if data is not used
- Fewer blocks -> more conflicts

### Reduce Miss Rate: Large Cache Size
Empirical Rule of Thumb: If cache size is doubled, miss rate usually drops by abour sqrt(2)

### Reduce Miss Rate: High Associativity
Empirical Rule of Thumb: Direct-mapped cache of size N has about the same miss rate as a 2-was set-associative cache of size N/2

## Cache Pipelining
### Write Performance
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/95a50ba3-93e6-4ea4-a347-31fe80b15c82)

We don't want to do this in 1 cycle, so we don't overwrite the data.

### Reducing Write Hit Time
Problem: writes take two cycles in memory stage, one cycle for tag check plus one cycle for data write if hit

Solutions:
- Design data RAM that can perform read and write concurrently, restore old value after tag miss
- Fully-associative (CAM Tag) caches: Word line only enable if hit
- Pipelined writes: Hold write data for store in single buffer ahead of cache, write cache data during next store's tag check
