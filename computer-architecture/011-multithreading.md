# Multithreading

## Reduction, Scatter/Gather, and the Cray 1

### Vector Supercomputers
- Scalar Unit
  - Load/Store Architecture
- Vector Extension
  - Vector Registers
  - Vector Instructions
- Implementation
  - Hardwired Control
  - Highly Pipelined Functional Units
  - Interleaved Memory System
  - No Data Caches
  - No Virtual Memory
 
Cray-1:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/20b28a45-f77e-4c52-8316-f9439ed89cb7)

### Cray-1
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/af4b8f71-923b-4ed5-9aaa-ceac481732c3)

## SIMD
### SIMD/Multimedia Extensions
- Q: How would a 32 bit adder change if we want to do 8 8-bit adds?
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ca864bff-674f-4a06-9efb-5190e2de8d24)
- Very short vectors added to existing ISAs for microprocessors
- Use existing 64-bit registers split into 2x32b or 4x16b or 8x8b
  - This concept first used on Lincoln Labs TX-2 computer in 1957, with 36b datapath split into 2x18b or 4x9b
  - Newer designs have 128-bit registers (PowerPC Altivec, Intel SSE2/3/4) or 256-bit registers (Intel AVX)
- Single instruction operates on all elements within register

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c603091f-c47e-4d79-a3ac-effc0a9ba8f2)

### Multimedia Extensions versus Vectors
- Q: What are some downsides of vectors compared to multimedia extensions?
  
- Limited instruction set:
  - no vector length control
  - no strided load/store or scatter/gather
  - unit-stride loads must be aligned to 64/128-bit boundary
- Limited vector register length:
  - requires superscalar dispatch to keep multiply/add/load units busy
  - loop unrolling to hide latencies increases register pressure
- Trend towards fuller vector support in microprocessors
  - Better support for misalighted memory accesses
  - Support of double-precision (64-bit floating-point)
  - New Interl AVX spec (announced April 2008), 256b vector registers (expandable up to 1024b)
 
## GPUs
### Graphics Processing Units (GPUs)
-
