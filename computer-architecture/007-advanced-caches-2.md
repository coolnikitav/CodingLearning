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
