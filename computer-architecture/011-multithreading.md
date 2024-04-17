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
- Q: Give a brief history of GPUs.
  
- Original GPUs were dedicated fixed-function devices for generating 3D graphics (mid-late 1990s) including high-performance floating-point units
  - Provide workstation-like graphics for PCs
  - User could configure graphics pipeline, but not really program it
- Over time, more programmability added (2001-2005)
  - E.g., New language Cg for writing small programs run on each vertex or each pixel, also Windows DirectX variants
  - Massively parallel (millions of vertices or pixels per frame) but very constrained programming model
- Some users noticed they could do general-purpose computation by mapping input and output data to images, and computation to vertex and pixel shading computations
  - Incredibly difficult programming model as had to use graphics pipeline model for general computation

### General Purpose GPUs (GPGPUs)
- In 2006, Nvidia introduced GeForce 8800 GPU supporting a new programming language: CUDa
  - "Compute Unified Device Architecture"
  - Subsequently, broader industry pushing for OpenCL, a vendor-neutral version of same ideas
- Idea: Take advantage of GPU computational performance and memory bandwidth to accelerate some kernels for general-purpose computing
- Attached processor model: Host CPU issues data-parallel kernels to GP-GPU for execution
- This lecture has a simplified version of Nvidia CUDA-style model and only considers GPU execution for computational kernels, not graphics

### Simplified CUDA Programming Model
- Q: Explain the general idea of the CUDA programming model.
  
- Computation performed by a very large number of independent small scalar threads (CUDA threads or microthreads) grouped into thread blocks

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/32d2f900-809f-41dd-b304-cf4266a65532)

### "Single Instruction, Multiple Thread"
- Q: What does Nvidia group 32 CUDA threads into?
  
- GPUs use a SIMT model, where individual scalar instruction streams for each CUDA thread are grouped together for SIMD execution on hardware (Nvidia groups 32 CUDA threads into a warp)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/01e2fd0b-8312-4018-ae3b-eee7297209c2)

### Implications of SIMT Model
- Q: Explain the SIMT model.

  
- All "vector" loads and stores are scatter-gather as individual microthreads perform scalar loads and stores
  - GPU adds hardware to dynamically coalesce individual microthread loads and stores to mimic vector loads and stores
- Every microthread has to perform stripmining calculations redundantly ("am I active?") as there is no scalar processor equivalent
- If divergent control flow, need predicates

### GPGPUs are Multithreaded SIMD
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d564abac-eb2d-43ff-ac51-be30940e2827)

### Nvidia Fermi GF100 GPU
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/84185c06-9d6b-47c0-886f-0f5417d2b1d9)

### Fermi "Streaming Multiprocessor" Core
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f1fe334b-203e-4316-b661-8733818c07e1)

## Multithreading Motivation
### Multithreading
- Q: Why is multithreading used?
  
- Difficult to continue to extract instruction-level parallelism (ILP) or data level parallelism (DLP) from a single sequential thread of control
- Many workloads can make use of thread-level parallelism (TLP)
  - TLP from multiprogramming (run independent sequential jobs)
  - TLP from multithreaded applications (run one job faster using parallel threads)
- Multithreading uses TLP to improve utilization of a single processor

### Pipeline Hazards
- Q: Think about all of potential solutions to this and why they dont work.
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d2cf6279-615a-4fa6-93a9-cccdaa675e0f)
- Answer: out of order superscalar, VLIW, going wide...
- Each instruction may depend on the next

What is usually done to cope with this?
- interlocks (slow)
- or bypassing (needs hardware, doesn't help all hazards)
