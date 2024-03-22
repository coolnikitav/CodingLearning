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

### Pipelining Cache Writes
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ee3cc6ea-b0b5-4ecc-aeea-d90c71bab6f4)

Data from a store hit written into data portion of cache during tag access of subsequent store.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/63c2777c-6273-40fd-8f11-9cd951f4e9c4)

### Pipelined Cache Efficacy
Cache Optimizations | Miss Rate | Miss Penalty | Hit Time | Bandwidth
 --- | --- | --- | --- | ---
 Pipelined Writes |  |  | - | +

 ## Write Buffer
 ### Write Buffer to Reduce Read Miss Penalty
 ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/561624ea-6c30-4c7e-a368-ff3968273e7b)

Processor is not stalled on writes, and read misses can go ahead of write to main memory

Problem: Write buffer may hold updated value of location needed by a read miss

Simple scheme: on a read miss, wait for the write buffer to go empty

Faster scheme: check write buffer addresses against read miss addresses, if no match,
allow read miss to go ahead of writes, else, return value in write buffer

### Write Buffer Efficacy
Cache Optimizations | Miss Rate | Miss Penalty | Hit Time | Bandwidth
 --- | --- | --- | --- | ---
 Write Buffer |  | + |  |

## Multilevel Caches
- Problem: A memory cannot be large and fast
- Solution: Increasing sizes of cach at each level

CPU <-> L1$ <-> L2$ <-> DRAM

- Local miss rate = misses in cache / accesses to cache
- Global miss rate = misses in cache / CPU memory access
- Misses per instruction = misses in cache / number of instructions

### Multilevel Caches
- Use smaller L1 if there is also L2
  - Trade increased L1 miss rate for reduced L1 hit time and reduced L1 miss penalty
  - Reduces average access energy
- Use simpler write-through L1 with on-chip L2
  - Write-back L2 cache absorbs write traffic, doesn't go off-chip
  - At most one L1 miss request per L1 access (no dirty victim write back) simplifies pipeline control
  - Simplifies coherence issues
  - Simplifies error recovery in L1 (can use just parity bits in L1 and reload from L2 when parity error detected on L1 read),
 
### Inclusion Policy
- Inclusive multilevel cache:
  - Inner cache holds copies of data in outer cache
  - External coherence snoop access need only check outer cache
- Exclusive multilevel caches:
  - Inner cache may hold data not in outer cache
  - Swap lines between inner/outer caches on miss
  - Used in AMD Athlon with 64KB primary and 256KB secondary cache
 
### Itanium-2 On-Chip Caches
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2af4bd9d-0f7c-401c-a59f-de4861f02e6b)

### Power 7 On-Chip Caches [IBM 2009]
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/922bb431-8e47-47c7-ad15-cedcfd7ea2f5)

### Multilevel Cache Efficacy L1, L2, L3
Cache Optimizations | Miss Rate | Miss Penalty | Hit Time | Bandwidth
      ---           |    ---    |     ---      |   ---    |   ---
 Multilevel Cache   |     +     |      +       |          |

## Victim Caches
### Victim Cache
- Small Fully Associative cache for recently evicted lines
  - Usually small (4-16 blocks)
- Reduced conflict misses
  - More associativity for small number of lines
- Can be checked in parallel or series with main cache
- On Miss in L1, Hit in VC: VC->L1,L1->VC
- On Miss in L1, Miss in VC: L1->VC, VC->? (Can always be clean)
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/34b161fe-e0c6-4c07-ab19-5d7c2fba50c4)

### Victim Cache Efficacy
Cache Optimizations | Miss Rate | Miss Penalty | Hit Time | Bandwidth
      ---           |    ---    |     ---      |   ---    |   ---
 Victim Cache       |     +     |      +       |          |

 ### Prefetching
 - Speculate on future instruction and data accesses and fetch them into cache(s)
   - Instruction accesses easier to predict than data accesses
 - Varieties of prefetching
   - Hardware prefetching
   - Software prefetching
   - Mixed schemes
 - What types of misses does prefetching affect?
   - Capacity and conflict miss in a negative way because you reduced your capacity by prefetching.
   - Helps compulsory miss by bringing in data preemptively.
  
### Issues in Prefetching
- Usefulness - should produce hits
- Timeliness - not late and not too early
- Cache and bandwidth pollution

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/38b33aab-a910-40ca-8017-c9f5008babad)

### Hardware Instruction Prefetching
Instruction prefetch in Alpha AXP 21064
- Fetch two blocks on a miss; the requested block (i) and the next consecutive block (i+1)
- Requested block placed in cache, and next block in instruction stream buffer
- If miss in cache but hit in stream buffer, move stream buffer block into cache and prefetch next block (i+2)
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1d78b22c-d965-4e85-9b6e-5bb4118eddcf)

### Hardware Data Prefetching
- Prefetch-on-miss:
  - Prefetch b+1 upon miss on b
- One Block Lookahead (OBL) scheme
  - Initiate prefetch for block b+1 when block b is accessed
- Strided prefetch
  - If observe sequence of accesses to block b, b+N, b+2N, then prefetch b+3N etc.
 
### Software Prefetching
```C
for (i = 0; i < N; i++) {
 prefetch(&a[i+1]);
 prefetch(&b[i+1]);
 SUM = SUM + a[i] * b[i];
}
```

### Software Prefetching Issues
- Timing is the biggest issue, not predictability
  - If you prefetch very close to when the data is required, you might be too late
  - Prefetch too early, cause pollution
 
### Prefetching Efficacy
Cache Optimizations | Miss Rate | Miss Penalty | Hit Time | Bandwidth
      ---           |    ---    |     ---      |   ---    |   ---
 Prefetching        |     +     |      +       |          |
