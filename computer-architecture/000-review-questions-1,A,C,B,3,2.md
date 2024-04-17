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

Same as a?

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

- a: There are 2 DRAM chips on the DIMM. Each DRAM chip has 36 I/Os.
- b: If there are 8B for data, we need burst length of 32B/8B = 4
- c: DDR2-667 is 5336 MB/sec and DDR2-533 is 4264 MB/sec

## 5 - https://www.cs.utexas.edu/~lorenzo/corsi/cs372/06F/hw/3sol.html

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
