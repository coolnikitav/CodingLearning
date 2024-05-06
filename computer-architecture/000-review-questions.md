- 1 - 4,9,10
- 2 - 9,11,13
- 3 - 1,13,14
- 4 - 9,10
- 5 - 19

## 16 - 4.12
The following kernel performs a portion of the finitedifference time-domain (FDTD) method for computing Maxwell’s equations
in a three-dimensional space, part of one of the SPEC06fp benchmarks:
```
for (int x=0; x<NX-1; x++) {
 for (int y=0; y<NY-1; y++) {
 for (int z=0; z<NZ-1; z++) {
 int index = x*NY*NZ + y*NZ + z;
 if (y>0 && x >0) {
 material = IDx[index];
 dH1 = (Hz[index] – Hz[index-incrementY])/dy[y];
 dH2 = (Hy[index] – Hy[index-incrementZ])/dz[z];
 Ex[index] = Ca[material]*Ex[index]+Cb[material]*(dH2-dH1);
}}}}
```
Assume that dH1, dH2, Hy, Hz, dy, dz, Ca, Cb, and Ex are all single-precision
floating-point arrays. Assume IDx is an array of unsigned int.

a) What is the arithmetic intensity of this kernel?

This code has a O(N^3) arithmetic intensity, since it has a triple nested for loop.

b) Is this kernel amenable to vector or SIMD execution? Why or why not?

This kernel can be executed both with vectors and SIMD. The same repetitive operation needs to be computed on the z array, then on the y, then on the x. Vectors and SIMD both work for this.

c)  Assume this kernel is to be executed on a processor that has 30
GB/sec of memory bandwidth. Will this kernel be memory bound or compute
bound?

In worst case scenario, we would need NX * NY * NZ * 8B. I am not sure if that would exceed 30GB/sec.

d) Develop a roofline model for this processor, assuming it has a
peak computational throughput of 85 GFLOP/sec.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0c77daa5-a1cd-4fff-96ba-2063aa87e8aa)





## 15 - 2.11
Consider the usage of critical word first and early restart on L2
cache misses. Assume a 1 MB L2 cache with 64 byte blocks and a refill path that
is 16 bytes wide. Assume that the L2 can be written with 16 bytes every 4 processor cycles, the time to receive the first 16 byte block from the memory controller
is 120 cycles, each additional 16 byte block from main memory requires 16
cycles, and data can be bypassed directly into the read port of the L2 cache.
Ignore any cycles to transfer the miss request to the L2 cache and the requested
data to the L1 cache.

a) How many cycles would it take to service an L2 cache miss with
and without critical word first and early restart?

Solution:
- 120 cycles with critical word first
- 120+3*16 = 168 cycles without critical word first

b) Do you think critical word first and early restart would be more
important for L1 caches or L2 caches, and what factors would contribute to
their relative importance?

It depends on the reduction in miss time for each cache.





## 14 - 5.19
Assume that we have a function for an application of the form F(i, p),
which gives the fraction of time that exactly i processors are usable given that a
total of p processors is available. That means that

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/50998839-cd7f-46a1-aaa0-00242d417c52)

Assume that when i processors are in use, the applications run i times faster. Rewrite
Amdahl’s law so it gives the speedup as a function of p for some application.

Answer:

Amdahl's law: speedup = Old execution time/New execution time

Old execution time = 1

New execution time = SUM(i=1 to p) of F(i,p)/i  because F(i,p) is old time and it can be reduced i times

So speedup = SUM(i=1 to p) of i/F(i,p)





## 13 - 4.10
In this problem, we will compare the performance of a vector processor with a hybrid system that contains a scalar processor and a GPU-based coprocessor. In the hybrid system, the host processor has superior scalar performance
to the GPU, so in this case all scalar code is executed on the host processor while
all vector code is executed on the GPU. We will refer to the first system as the
vector computer and the second system as the hybrid computer. Assume that your
target application contains a vector kernel with an arithmetic intensity of 0.5
FLOPs per DRAM byte accessed; however, the application also has a scalar component which that must be performed before and after the kernel in order to prepare the input vectors and output vectors, respectively. For a sample dataset, the
scalar portion of the code requires 400 ms of execution time on both the vector
processor and the host processor in the hybrid system. The kernel reads input
vectors consisting of 200 MB of data and has output data consisting of 100 MB
of data. The vector processor has a peak memory bandwidth of 30 GB/sec and
the GPU has a peak memory bandwidth of 150 GB/sec. The hybrid system has an
additional overhead that requires all input vectors to be transferred between the
host memory and GPU local memory before and after the kernel is invoked. The
hybrid system has a direct memory access (DMA) bandwidth of 10 GB/sec and
an average latency of 10 ms. Assume that both the vector processor and GPU are performance bound by memory bandwidth. Compute the execution time required
by both computers for this application.

Answer:

Vector processor vs hybrid (scalar host processor with a GPU-based coprocessor)

Application: scalar component (400ms) -> vector kernel (arithmetic intensity of 0.5 FLOPs per DRAM B accessed) -> scalar component (400 ms)

Vector processor: Execution time = 400ms (for scalar execution) + (200MB + 100MB)/(30GB/sec) = 410ms

Hybrid processor: Execution time = 400ms + (200MB+100MB)/(10GB/sec) + (200MB+100MB)/(150GB/sec) = 400 + 30 + 2 = 432ms





## 12 - 2.9
Problem deleted.





## 11 - 1.10
Server farms such as Google and Yahoo! provide enough
compute capacity for the highest request rate of the day. Imagine that most of the
time these servers operate at only 60% capacity. Assume further that the power
does not scale linearly with the load; that is, when the servers are operating at
60% capacity, they consume 90% of maximum power. The servers could be
turned off, but they would take too long to restart in response to more load.
A new system has been proposed that allows for a quick restart but requires 20%
of the maximum power while in this “barely alive” state.

a) How much power savings would be achieved by turning off 60% of the servers?

If we turn off 60% of the servers, 60% of power will be saved.

b) How much power savings would be achieved by placing 60% of the servers in the “barely alive” state?

Pnew/Pold = (60*20 + 40*90)/(100*90) = (1200+3600)/(9000) = 4800/9000 = 53.3%, so 46.7% savings

c) How much power savings would be achieved by reducing the voltage by 20% and frequency by 40%?

Power is proportional to voltage squared and frequency

So Pnew/Pold = (0.8)^2*0.6/1 = 0.64*0.6 = 0.384, or 61.6% savings

d)  How much power savings would be achieved by placing 30% of the servers in the “barely alive” state and 30% off?

Pnew/Pold = (30*20 + 30*0 + 40*90) / (100*90) = (4200)/(9000) = 0.467, or 53.3% savings





## 10 - 3.13
Problem deleted.





## 9 - 4.9

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f32c40f0-1a12-4fa1-bf69-bce238d5d79d)

a) What is the arithmetic intensity of this kernel? Justify your answer.
  
Arithmetic intensity is the ratio of floating-point operations to memory bytes accessed. This code reads 4 floats and writes 2 floats for every 6 FLOPS, so arithmetic intensity = 6/6 = 1.

b) Convert this loop into VMIPS assembly code using strip mining.
```
LD VL, #44  ; 300 % 64
LD R1, #64
loop:
LV V1, a_re+R1
LV V2, b_re+R1
MULVV.S V3, V1, V2
LV V4, a_im+R1
LV V5, b_im+R1
MULVV.S V6, V4, V5
SUBVV.S V6, V3, V6
SV V6, c_re+R1
MULVV.S V7, V1, V5
MULVV.S V8, V4, V2
ADDVV.S V8, V8, V7
SV V8, c_im+R1
BNE R1, 0, else  ; fist iteration increment by 44
ADDI R1, R1, #44
LD VL, #64  ; load MVL back in
j loop
else:
ADDI R1, R1, #64
BLT R1, 300, loop
```

c) Assuming chaining and a single memory pipeline, how many chimes are required? How many clock cycles are required per complex result value, including start-up overhead?

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a5eee697-b581-411d-9e6c-261ac8e103ec)

d) If the vector sequence is chained, how many clock cycles are required per complex result value, including overhead?

total cycles per iteration = 6 chimes * 64 elements + 15 cycles (load/store) * 6 + 8 cycles (multiply) * 4 + 5 cycles (add/sub) *2 = 516

cycles per result = 516/128 = 4

e) Now assume that the processor has three memory pipelines and chaining. If there are no bank conflicts in the loop’s accesses, how many clock cycles are required per result?

3 memory pipelines would allow 3 load/stores to occur at the same time. So the pipeline can be shorted by about 6 load/stores, or 6 cycles, resulting in 42 cycles.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ab520c43-ccb0-4b39-8fec-7b59d5889917)


## 8 - 1.9
You are designing a system for a real-time application in which
specific deadlines must be met. Finishing the computation faster gains nothing.
You find that your system can execute the necessary code, in the worst case,
twice as fast as necessary.
- a: How much energy do you save if you execute at the current speed
and turn off the system when the computation is complete?

Energy is proportional to voltage squared. Also, if you want to execute at current speed, it is 50% less than twice as fast, requiring 50% less voltage.

Energy_new/Energy_old = (voltage*0.5)^2/(voltage)  = 0.25

Since the process is running 2 times longer, multiply the ratio by 2. So you save 50% energy.

- b: How much energy do you save if you set the voltage and frequency to be half as much?

Energy is proportional to Voltage squared. Frequency does not affect energy, only power. So the new energy is (1/2V)^2 = 25%

## 7 - 3.14
In this exercise, we look at how software techniques
can extract instruction-level parallelism (ILP) in a common vector loop. The following loop is the so-called DAXPY loop (double-precision aX plus Y) and
is the central operation in Gaussian elimination. The following code implements the DAXPY operation, Y = aX + Y, for a vector length 100. Initially, R1 is
set to the base address of array X and R2 is set to the base address of Y:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/11fa04f4-161c-49bf-88a1-1191587983f8)

Assume the functional unit latencies as shown in the table below. Assume a onecycle delayed branch that resolves in the ID stage. Assume that results are fully
bypassed. 

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/457862ff-e313-4c3d-af89-5c29c96a4d4f)

a.

Solution doesn't make sense.

Unscheduled:
- L.D    F2,0(R1)
- Stall
- Stall
- MUL.D  F4,F2,F0
- Stall
- Stall
- Stall
- Stall
- Stall
- Stall
- L.D    F6,0(R2)
- Stall
- Stall
- ADD.D  F6,F4,F6
- Stall
- Stall
- Stall
- Stall
- S.D    F6,0(R2)
- Stall
- Stall
- DADDIU R1,R1,#8
- Stall
- Stall
- DADDIU R2,R2,#8
- Stall
- Stall
- DSLTU  R3,R1,R4
- Stall
- Stall
- BNEZ R3,foo
- Stall

Scheduled:
- L.D    F2,0(R1)
- L.D    F6,0(R2)
- Stall
- MUL.D  F4,F2,F0
- DADDIU R1,R1,#8
- DADDIU R2,R2,#8
- DSLTU  R3,R1,R4
- Stall
- Stall
- Stall
- ADD.D  F6,F4,F6
- Stall
- Stall
- Stall
- Stall
- S.D    F6,0(R2)
- Stall
- Stall
- BNEZ R3,foo
- Stall

Execution time:
- Unscheduled: 32 cycles
- Scheduled: 20 cycles

The clock would have to be 32/20 = 1.6, or 60% faster to match the performance improvement achieved by scheduling.

b.

Solution doesn't make sense.

The loop must be unrolled 7 times because there are 6 stall slots after MUL.D

Instruction schedule:
- L.D    F2,0(R1)
- L.D    F8,8(R1)
- L.D    F14,16(R1)
- L.D    F20,24(R1)
- L.D    F26,32(R1)
- L.D    F32,40(R1)
- L.D    F38,48(R1)
- MUL.D  F4,F2,F0
- MUL.D  F10,F8,F0
- MUL.D  F16,F14,F0
- MUL.D  F22,F20,F0
- MUL.D  F28,F26,F0
- MUL.D  F34,F32,F0
- MUL.D  F40,F38,F0
- L.D    F1,0(R2)
- L.D    F7,8(R2)
- L.D    F13,16(R2)
- L.D    F19,24(R2)
- L.D    F25,32(R2)
- L.D    F31,40(R2)
- L.D    F37,48(R2)
- ADD.D  F1,F4,F1
- ADD.D  F7,F10,F7
- ADD.D  F13,F16,F13
- ADD.D  F19,F22,F19
- ADD.D  F25,F28,F25
- ADD.D  F31,F34,F31
- ADD.D  F37,F40,F37
- S.D    F1,0(R2)
- S.D    F7,8(R2)
- DADDIU R1,R1,#56
- S.D    F13,16(R2)
- S.D    F19,24(R2)
- DADDIU R2,R2,#56
- S.D    F25,32(R2)
- S.D    F31,40(R2)
- DSLTU  R3,R1,R4
- S.D    F37,48(R2)
- BNEZ R3,foo

39 cycles for 7 elements, so 5.57 cycles per element

c.

Solution doesn't make sense.

Mem ref 1 | Mem ref 2 | FP op 1 | FP op 2 | Integer op/branch
 --- | --- | --- | --- | ---
 L.D    F2,0(R1)   | L.D    F20,24(R1) |                    |                    |
 L.D    F8,8(R1)   | L.D    F26,32(R1) |                    |                    |
 L.D    F14,16(R1) | L.D    F32,40(R1) | MUL.D  F4,F2,F0    | MUL.D  F22,F20,F0  |
 L.D    F1,0(R2)   | L.D    F19,24(R2) | MUL.D  F10,F8,F0   | MUL.D  F28,F26,F0  |
 L.D    F7,8(R2)   | L.D    F25,32(R2) | MUL.D  F16,F14,F0  | MUL.D  F34,F32,F0  |
 L.D    F13,16(R2) | L.D    F31,40(R2) | ADD.D  F1,F4,F1    | ADD.D  F19,F22,F19 |
   .               |  .                | ADD.D  F7,F10,F7   | ADD.D  F25,F28,F25 |
   .               |  .                | ADD.D  F13,F16,F13 | ADD.D  F31,F34,F31 | DADDIU R1,R1,#48
 S.D    F1,0(R2)   | S.D    F19,24(R2) |                    |                    | DADDIU R2,R2,#48
 S.D    F7,8(R2)   | S.D    F25,32(R2) |                    |                    | DSLTU  R3,R1,R4
 S.D    F13,16(R2) | S.D    F31,40(R2) |                    |                    | BNEZ R3,foo

 Does 6 elements in 11 cycles, so execution time per element is 1.83 cycles per element. 34 out of 55 cycles are used. It uses 19 registers.

## 6 - 2.13
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8fcbb4f4-0c9f-4a67-93a0-1bc519b5d56b)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b83a711c-da84-41b5-835c-b1837fd88f35)

- a: A 2GB DRAM with parity or ECC effectively has 9 bit bytes. This would require 18 1Gb DRAMs. To create 72 output bits, each one would need to output 72/18 = 4 bits.
- b: If there are 8B for data, we need burst length of 32B/8B = 4
- c: DDR2-667 is 667 * 8 = 5336 MB/sec and DDR2-533 is 533 * 8 = 4264 MB/sec

## 5 - https://www.cs.utexas.edu/~lorenzo/corsi/cs372/06F/hw/3sol.html

1 - ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b6f3dd23-de2d-490b-b1ab-bdb4b4d9bc1b)

1.1 - What is the page size in such a system?

There are 8 bits for offset, so page size is 2^8B.

1.2 - What is the size of a page table for a process that has 256K of memory starting at address 0?

256KB = 2^18B, or 2^10 pages

Each L3 table address 2^6 pages, so we need 2^4 L3 tables.

Each L2 table addresses 2^8 L3 tables, so we only need 2^4 entries in 1 L2 table.

Since we only need 1 L2 table, we need 1 entry in the L1 table.

Assuming 2B per entry, we need 1 * 2^10 * 2 + 1 * 2^8 * 2 + 2^4 * 2^6* 2 = 4608B.

2 - A computer system has a 36-bit virtual address space with a page size of 8K, and 4 bytes per page table entry.

2.1 - How many pages are in the virtual address space?

2^36 / 2^13 = 2^23 pages

2.2 - What is the maximum size of addressable physical memory in this system?

We can reference 2^32 pages with 36 bit virtual address and 4B per PTE. Thus, max size of physical addressable memory is 2^32 * 2^13 = 2^45

2.3 - If the average process size is 8GB, would you use a one-level, two-level, or three-level page table? Why?

8GB = 2^33B, Page size = 2^13B

One-level:

If we have one table, it would have 2^23 PTE. If each of them is 4B, we would need 2^25, or 32MB of memory.

Two-level:

V.A is 36 bits, offset is 13 bits. Thus, 23 bits remaining: 11 for L2 tables, 12 for L1 table.

We need 2^33/2^13 = 2^20 pages => 2^20/2^11 = 2^9 L2 tables

1 * 2^12 * 4 + 2^9 * 2^11 * 4 = 2^13 + 2^22 = ~4MB

Three-level:

V.A split: 8,8,7,13

We need 2^20 pages => 2^20 / 2^7 = 2^13 L3 tables => 2^13/2^8 = 2^5 L2 tables => 2^5 entries in 1 L1 table

1 * 2^8 * 4 + 2^5 * 2^8 * 4 + 2^13 * 2^7 * 4 = ~4MB

It is better to pick level 2 because it has less overhead than leve 3, while using the same amount of memory.

3 - In a 32-bit machine we subdivide the virtual address into 4 pieces as follows:
8-bit    4-bit    8-bit    12-bit
We use a 3-level page table, such that the first 8 bits are for the first level and so on. Physical addresses are 44 bits and there are 4 protection bits per page.

3.1 - What is the page size in such a system?

Page size = 2^12B

3.2 - How much memory is consumed by the page table and wasted by internal fragmentation for a process that has 64K of memory starting at address 0?

64KB = 2^16B or 2^4 pages. Thus, we need 2^4 entries in 1 L3 table, 1 entry in 1 L2 table, 1 entry in 1 L1 table.

Page frame number = 2^44 / 2^12 = 2^32, adding 4 protection bits, each entry of level 3 would need to be 36 bits. Rounding to 64 bits, or 8B.

Memory consumed: 1 * 2^8 * 8 + 1 * 2^4 * 8 + 1 * 2^8 * 8 = 2048B

## 4 - 3.1
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ebc33478-ee37-4e16-bfdd-004f5ba9bfd6)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7e911438-e85d-4224-a0dd-23b5986f4120)

If you cannot issue an instruction until the previous one is completed, there is no pipelining.

4+12+5+4+1+1+0+0+1+0+1+1(delay slot) = 30 cycles

Solution:

Each instruction takes 1 cycles to execute + extra latency cycles.

(1+4)+(1+12)+(1+5)+(1+4)+(1+1)+(1+1)+(1+0)+(1+0)+(1+1)+(1+0)+(1+1) = 40 cycles

## 3 - A.1
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/79e01d59-65c1-412b-9c83-fcbeca14995f)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/6698e028-bcd0-4bbc-a915-4832f2dab383)

- load/store:
  - gap: 26.5 + 10.3 = 36.8%
  - gcc: 25.1 + 13.2 = 38.3%
  - average: (36.8+38.3)/2 = 37.55%
- alu instructions (add, sub, mul, compare, load imm, shift, AND, OR, XOR, other logical)
  - gap: 21.1 + 1.7 + 1.4 + 2.8 + 4.8 + 3.8 + 4.3 + 7.9 + 1.8 + 0.1 = 49.7%
  - gcc: 19.0 + 2.2 + 0.1 + 6.1 + 2.5 + 1.1 + 4.6 + 8.5 + 2.1 + 0.4 = 46.6%
  - average: 48.15%
- conditional branches:
  - gap: 9.3%
  - gcc: 12.1%
  - average: 10.7%
- jumps:
  - gap: 0.8%
  - gcc: 0.7%
  - average: 0.75%
 
CPI = 1.0 * 0.4815 + 1.4 * 0.3755 + 2.0 * 0.6 * 0.107 + 1.5 * 0.4 * 0.107 + 1.2 * 0.0075 = 0.4815 + 0.5257 + 0.1284 + 0.0642 + 0.009 = 1.2088

## 2 - 1.4
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/974d3f7c-608b-4ea9-ab45-03aaa225bf7d)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/dd261a1e-45ab-4a76-8467-4602f1e459b4)

a.

Power needed = 66 + 2*2.3 + 7.9 = 78.5 W

Power supply is 80% efficient, so it should be 78.5/0.8 = 99 W

b.

power = 0.6*4 + 0.4*7.9 = 2.4 + 3.16 = 5.56

c.

seek7200 = 0.75 * seek5400

seek7200 + idle7200 = 100

seek5400 + idle5400 = 100

seek7200 * 7.9 + idle7200 * 4 = seek5400 * 7 + idle5400 * 2.9

idle5400 = 29.8%

## 1-H&P Ch 1.9
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/240a927a-acc1-4307-a87e-8188a0dffcc5)

Speedup = (old execution time)/(new execution time)

(old execution time) = 1

(new execution time) = 0.6 + 0.4/10 (it will spend 10 times less time on the 40% part)

speedup = 1/0.64 = 1.56
