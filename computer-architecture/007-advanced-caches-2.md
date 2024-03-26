# Advanced Caches 2
## Multiporting and Banking
### Increasing Cache Bandwidth: Multiporting and Banking
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3dd61b1b-9090-444b-88d3-0a6cb1eecd1d)

Challenge: Two stores to the same line, or Load and Store to same line

### True Multiport Caches
- Large area increase (coule be double for 2-port)
- Hit time increase (can be made small)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/12fbfe07-d488-42c8-b4b7-25783c65bd06)

### Banked Caches
- Partition Address Space into multiple banks
  - Use portions of address (low or high order interleaved)
 
Benefits:
- Higher throughput
Challenges:
- Bank conflicts
- Extra wiring
- Uneven utilization

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f801afa2-79b3-432f-8562-237cff319c0a)

### Cache Banking Efficacy
Cache Optimizations | Miss Rate | Miss Penalty | Hit Time | Bandwidth
 --- | --- | --- | --- | ---
 Cache Banking |  |  |  | +

## Software Memory Optimizations
### Compiler Optimizations
- Restructuring code affects the data block access sequence
  - Group data accesses together to improve spatial locality
  - Re-order data accesses to improve temporal locality
- Prevent data from entering the cache
  - Useful for variables that will only be accessed once before being replaced
  - Needs mechanism for software to tell hardware not to cache data ("no-allocate" instruction hints or page table bits)
- Kill data that will never be used again
  - Streaming data exploits spatial locality but not temporal locality
  - Replace into dead cache locations

### Loop Interchange
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/52e83493-a63a-4ba0-892e-dd029d44c1b3)

This improves spatial locality.

### Loop Fusion
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/af355f14-8e31-4ab7-9c73-9526ded58969)
- Problem: when the second loop starts a[0] will already be discarded

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/5fb9dcdc-0b71-4974-b2ae-b7f1f8e64198)

Improves temporal locality

### Matrix Multiply, Naive Code
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f895d6e5-4d1a-4713-89fe-b67345465cf8)

### Matrix Multiply with Cache Tiling/Blocking
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/9cd99923-f809-4853-9515-bdd6278820f7)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/aa75c87f-d8ad-4a10-b548-4ea9554ec676)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ba04e230-2d2d-4bde-bb39-d60a4092b3f9)

Better temporal and spatial locality

### Compiler Memory Optimizations Efficacy
Cache Optimizations | Miss Rate | Miss Penalty | Hit Time | Bandwidth
 --- | --- | --- | --- | ---
 Compiler Optimization |  | + |  | 

## Non-blocking Caches
### Non-Blocking Caches (aka Out-Of-Order Memory System) (aka Lockup Free Caches)
- Enable subsequent cache accesses after a cache miss has occurred
  - Hit-under-miss
  - Miss-under-miss (concurrent misses)
- Suitable for in-order processor or out-of-order processors
- Challenges
  - Maintaining order when multiple misses that might return out of order
  - Load or Store to an already pending miss address (need merge)
 
### Non-Blocking Cache Timeline
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/023865cb-f4ae-4093-a524-e5af977671a8)

### Miss Status Handling Register (MSHR) / Miss Address File (MAF)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e4d3c04c-f011-4d5a-86d9-b6e4806fe9f6)

### Non-Blocking Cache Operation
On cache miss:
- Check MSHR for matched address
  - If found: allocate new load/store entry pointing to MSHR
  - If not found: allocate new MSHR entry and Load/Store entry
  - If all entries full in MSHR or Load/Store entry table, stall or prevent new LDs/STs

On data return from memory:
- Find load or store waiting for it
  - Forward load data to processor/Clear store buffer
  - Could be multiple loads and stores
- Write data to cache

When cache lines is completely returned:
- De-allocated MSHR entry

### Non-Blocking Cache with In-Order Pipelines
- Need scoreboard for individual registers

On load miss:
- Mark destination register as busy

On load data return:
- Mark destination register as available

On use of busy register
- Stall processor

### Non-Blocking Cache Efficacy
Cache Optimizations | Miss Rate | Miss Penalty | Hit Time | Bandwidth
 --- | --- | --- | --- | ---
 Non-Blocking Cache |  | + |  | +

 ## Critical Word First and Early Restart
 ### Critical Word First
- Request the missed word from memory first
- Rest of cache line comes after "critical word"
  - Commonly words come back in rotated order

 ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b056d472-31c4-444c-bdb4-0200e9b68336)

### Early Restart
- Data returns from memory in order
- Processor restarts when needed word is returned
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8c20c8e2-fca5-4feb-937a-d26582c187c2)
