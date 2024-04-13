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

### Virtually Addressed Cache (Virtual Index/Virtual Tag)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/448d12a6-7d4e-482f-8a1b-9f0ba4e7e07f)

### Aliasing in Virtual-Address Caches
- Q: Explain what aliasing is in this context.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/dc65b5fc-5398-4a2e-83ef-6a50b509761c)

- General solution: Prevent aliases coexisting in cache
- Software (i.e, OS) solution for direct-mapped cache: VAs of shared pages must agree in cache index bits; this ensures all VAs accessing same PA will conflict in direct-mapped cache (early SPARCs)

### Cache-TLB Interactions
- Physically Indexed/Physically Tagged
- Virtually Indexed/Virtually Tagged
- Virtuall Indexed/Physicaly Tagged
  - Concurrent cache access with TLB Translation
- Both Indexed/Physically Tagged
  - Small enough cache or highly associative cache will have fewer indexes than page size
  - Concurrent cache access with TLB Translation
 
## Vector Processor Introduction
### Vector Programming Model
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e55e6831-fe7b-4160-a634-6d0d79b1b84f)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a3be3bcd-dcea-407c-b782-559626685c75)
