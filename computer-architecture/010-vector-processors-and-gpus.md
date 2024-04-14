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
- Q: Explain what ADDVS V3,V1,#1 does.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e55e6831-fe7b-4160-a634-6d0d79b1b84f)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a3be3bcd-dcea-407c-b782-559626685c75)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/5310042b-937a-4773-9b35-c3fa3ff27fa4)

### Vector Code Element-by-Element Multiplication
- Q: show what this C code would look like in Scalar assembly code and Vector assembly code:

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/049060a8-1570-403d-b199-355df278aec0)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/557ec859-1cf0-48e5-8865-6b53bb44b8af)

### Vector Arithmetic Execution
- Q: Why does vector execution not need bypassing?
  
- Use deep pipeline (=> fast clock) to execute element operations
- Simplifies control of deep pipeline because elements in vector are independent
  - No data hazards!
  - No bypassing needed

This has a 6 stage multiply pipeline:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/56547519-3510-46d3-9014-73daa2402ea1)

### Interleaved Vector Memory System
- Q: What is bank busy time?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b1dffd60-abf0-4d36-9fe9-aa446f3204e6)
