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

## Vector Parallelism
### Example Vector Microarchitecture
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0f2e5643-ab47-43a9-b5e8-5e08e140f2cc)

### Basic Vector Execution
- Q: What is a chime?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b7b2e4da-8032-4e9c-87e9-74ba60a470de)

Chime - how long it takes to execute a vector instruction on an architecture.

### Vector Instruction Parallelism
- Can overlap execution of multiple vector instructions
  - Example machine has 32 elements per vector register and 8 lanes
 
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/229bed20-6b1d-4cfb-9af9-39e3347bfec4)

## Vector Hardware Optimizations
### Vector Chaining
- Q: What is vector chaining and what is its equivalent in scalar processors?
- Vector version of register bypassing
  - Introduce with Cray-1
 
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d64fadb7-a2ac-4483-9849-758925706cb8)

You don't have to wait for the first operation to get through the whole vector before starting second operation.

### Vector Chaining Advantage
- Without chaining, must wait for last element of result to be written before starting dependent instruction

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/24273257-4d2f-4616-935e-d312a33932c4)
  
- With chaining, can start dependent instruction as soon as first result appears
  
  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e73f50e8-674b-4c86-8d2b-e2bc615f92c0)

### Chaining (Register File) Vector Execution
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e0a651a2-3ce9-404f-a99b-f8fee42ac69a)

### Chaining (Bypass Network) Vector Execution
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e0a651a2-3ce9-404f-a99b-f8fee42ac69a)

### Chaining (Bypass Network) Vector Execution and More RF Ports
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/de218261-a44f-40c0-b010-c11b00d68bc7)

### Vector Stripmining
- Q: What is stripmining?
- Problem: Vector registers have finite length
- Solution: Break loops into pieces that fit in registers, "Stripmining"

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/68eb7002-06db-4606-84fb-c8bc7f918f36)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/de53828a-2bbd-476c-bdb4-0cb1db8a01bd)

### Vector Instruction Execution
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c3c2c1cc-b8bb-4fd4-9650-209eb349711d)

### Two Lane Vector Microarchitecture
- Q: What does a 2 lane microarchitecture look like?

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/73268ed5-9ac3-45a3-851f-ba3288391faa)

### Vector Stripmining - 2 Lanes
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/6ebc4e1d-0a23-4691-8118-0864bc3438b3)

### Vector Unit Structure
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e094e2e2-2664-4588-9ecd-161f31adccc7)

### T0 Vector Microprocessor
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c6fe2b21-e522-4cce-a6ed-e7381d57f132)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/65ae9054-0b79-4277-a58d-8e9585b3c01e)

### Vector Instruction Set Advantages
- Q: What do vector instructions tell hardware (6 things)?
- Compact
  - One short instruction encodes N operations
- Expressive, tells hardware that these N operations:
  - are independent
  - use the same functional unit
  - access disjoint registers
  - access registers in same pattern as previous instructions
  - access a contiguous block of memory (unit-stride load/store)
  - access memory in a known pattern (strided load/store)
- Scalable
  - can run same code on more parallel pipelines (lanes)
 
## Vector Software and Compiler Optimizations

### Automatic Code Vectorization
- Q: What is vectorization?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a326ee22-c777-4567-a9b5-55b5b93b95e9)

Vectorization is a massive compile-time reordering of operation sequencing -> requires extensive loop dependence analysis

### Vector Conditional Execution
- Q: How to vectorize loops with conditional code?
  
- Problem: Want to vectorize loops with conditional code:

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/dcb4e117-5da2-4335-8c90-27b6641de9a1)

- Solution: Add vector mask (or flag) registers
  - vector version of predicate registers, 1 bit per element
- ... and maskable vector instructions
  - vector operation becomes NOP at elements where mask bit is clear

Code example:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d350a2e1-cbdb-4b82-8f88-c2b64b005b59)

### Masked Vector Instructions
- Q: What is the simple implementation and what is the density-time implementation?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3ce219a8-43f9-4841-abd7-45d58850e345)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/138cb047-d8a4-4bb8-b3f7-826c94a08bdf)

### Vector Reductions
Problem: Loop-carried dependence on reduction variables

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/99c564de-717c-4207-98d6-b97047116e19)

Solution: Re-associate operations if possible, use binary tree to perform reduction

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e11f785d-dc62-493b-b903-a78aba35dcec)

### Vector Scatter/Gather
- Q: What is scatter and gather?
  
Want to vectorize loops with indirect accesses:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/35007557-b34e-403b-9ec0-e12e17b49db1)

Indexed load instruction (Gather)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/32e6f881-b0af-434b-8fc5-3180654ffd69)
