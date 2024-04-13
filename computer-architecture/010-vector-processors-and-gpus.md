# Vector Processors and GPUs

## Address Translation Review

### Address Translation in CPU Pipeline
- Q: how to cope with additional latency of TLB?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f9512ad9-8a40-40ad-8b45-68b536072441)

- Software handlers need restartable exception on TLB fault
- Handling a TLB miss needs a software or a hardware mechanism to refill the TLB
- Need to cope with additional latency of TLB:
  - slow down the clock?
  - pipeline the TLB and cache access?
  - virtual address caches
  - parallel TLB/cache access
 
## Cache and Memory Protection Interaction

### Virtual-Address Caches
- Q: what are pros and cons of rearranging the cache and TLB?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/6b10bcd9-35ac-4ab7-8337-44dc2fa1b92c)

- One-step process in case of a hit (+)
- Cache needs to be fluhsed on a context switch unless address space identifies (ASIDs) included in tage (-)
- Aliasing problems due to the sharing of pages (-)
- Maintaining cache coherence (-)
