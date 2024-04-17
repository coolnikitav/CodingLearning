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

### Coarse-Grain Multithreading
- Q: How can we guarantee no dependencies between instructions in a pipeline?
- A: One way is to interleave execution of instructions from different program threads on the same pipeline.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f3730e61-b7e8-45dc-ba9c-a408a772f20f)

### Simple Multithreaded Pipeline
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/bb5e11c4-45a5-49e2-8804-158e72f4f8c7)
- Have to carry thread select down pipeline to ensure correct state bits read/written at each pipe stage
- Appears to software (including OS) as multiple, albeit slower, CPUs

### Multithreading Costs
- Q: What does each thread require?
  
- Each thread requires its own user state
  - PC
  - GPRs
- Also, needs its own system state
  - Virtual memory page table base register
  - Exception handling registers
- Other overheads:
  - Additional cache/TLB conflicts from competing threads
  - (or add larger cache/TLB capacity)
  - More OS overhead to schedule more threads (where do all these threads come from?)
 
### Thread Scheduling Policies
- Q: What are the 3 scheduling policies? Explain what each of them does.
  
- Fixed interleave
  - Each of N threads executes one instruction every N cycles
  - If thread not ready to go in its slot, insert pipeline bubble
  - Can potentially remove bypassing and interlocking logic

    ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/fe52ec0b-3897-4d2d-b6ea-470f122d2c94)

- Software-controlled interleave
  - OS allocates S pipeline slots amongst N threads
  - Hardware performs fixed interleave over S slots, executing whichever thread is in that slot

    ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2dc47187-7ca8-4681-a0a7-1f81e57f9fba)

- Hardware-controlled thread scheduling
  - Hardware keeps track of which threads are ready to go
  - Picks next thread to execute based on hardware priority scheme

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/975d9f17-6058-461b-8841-f0f08f4a9362)

### Coarse-Grain Hardware Multithreading
- Some architectures do not have many low-latency bubbles
- Add support for a few threads to hide occasional cache miss latency
- Swap threads in hardware on cache miss

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f3daf936-420a-4259-b5af-847f6a159545)

### Denelop HEP
- Q: How could HEP issue a load or a store on every instruction and not run into memory latency issues?
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/85139382-5027-4b27-be64-56efd97088a2)

First commercial machine to use hardware threading in main CPU
- 120 threads per processor
- 10 MHz clock rate
- Up to 8 processors
- Precursor to Tera MTA (Multithreaded Architecture)

Each processor had 120 threads and memory latency was not more than 120 cycles. So you could issue a load or store on every instruction.

### Tera (Cray) MTA (1990)
- Q: Why did the processor demand so much power?

- Up to 256 processors
- Up to 128 active threads per processor
- Processors and memory modules populate a sparse 3D torus interconnection fabric
- Flat, shared main memory
  - No data cache
  - Substrains one main memory access per cycle per processor
- GaAs logic in prototype, 1KW/processors @ 260 MHz
  - Seconds version CMOS, MTA-2, 50W/processor
  - New version, XMT, fits into AMD Opteron socket, runs at 500 MHz

- A: Locality is not exploited at all and going to the main memory every cycle.

### MTA Pipeline
- Every cycle, one VLIW instruction from one active thread is launched into pipeline
- Instruction pipeline is 21 cycles long
- Memory operations incur ~150 cycles of latency

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/69044f4d-9dd6-4596-bcba-989d0d2949d6)

### MIT Alewife (1990)
- Modified SPARC chips
  - register windows hold different thread contexts
- Up to four threads per node
- Thread switch on local cache miss

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a0cc096c-fb1c-47f2-aa0e-e584925c5f9c)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/93968630-bafd-4d38-b2e0-40a9811bd7b4)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/9e3a4826-f3fa-40ff-889f-b6870aeea054)
