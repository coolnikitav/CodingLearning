# Multicycle Operations
- Certain instructions (e.g., mul, div, FP operations) do not execute in 1 cycle
  
  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/47a3ee0d-28d0-4d61-aacb-f663d5fc8e7c)
- Must handle multicycle operations
  - Introduce several execution pipelines
  - Allow multiple outstanding operations
### Multiple Functional Units
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d8d2ace7-3da0-4108-b86a-1dd0e18b82fe)

### Pipeline Supporting Multiple Outstanding FP Operations
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ba3bc853-2270-419c-911e-990e037105d4)

### Latency and Initiation Interval
- Latency: # cycles between instr that produces result and instr that uses it
- Initiation or repeat interval: # cycles between issuing 2 instrs of same type
  
Functional Unit | Latency | Initiation Interval | Explanation
--- | --- | --- | ---
Int ALU | 0 | 1 | Result can be used next cycle (forwarding)
Data memory | 1 | 1 | Load-use
FP adder | 3 | 1 | FP add takes 4 cycles but is pipelined
Multiplier | 5 | 1 | Mul takes 6 cycles but is pipelined
Divider | 24 | 25 | Div takes 25 cycles and is not pipelined

### Latency and Initiation Interval FP Adder
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/4a2a01c4-7b01-46ff-bde4-b324cb468373)

# Challenges for Longer Pipelines
### Hazards in Longer Pipelines
- Divider not pipelined -> structurla hazards can occur
- Instructions varying latencies -> # register writes in a cycle can be > 1
- Instructions do not always reach WB in order -> write-after-write (WAW) hazards possible
- Instructions can complete out of order -> exceptions problematic
- Longer latency -> more stalls due to RAW hazards
- Complexity of forwarding logic increases

### Source
- *Structural hazard*: divider not pipelined
- *Solution*: Detect it and stall next DIV instruction
  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f8a87a6b-3034-486a-bb50-8236a11076c9)

### Hazards in Longer Pipelines
- *Structural hazard*: due to varying latencies, >1 instructions may write to RF (register file) in same cycle
  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/635093f4-f05f-4d21-ae63-7051ca1db4ec)
- *Solutions*: Stall or increase number of write ports
  - Cannot happen if instructions pass MEM stage sequentially

### WAW Hazards in Longer Pipelines
- Because instructions do not always write back in order, WAW hazards are possible
  - Later instr writes register Rn before earlier instr writes Rn
  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2dc077af-164e-47dc-b44d-79dfdc122e5d)
  - Next instr may read wrong value
  - *Potential solution*: if instr inID wants to write same register as instr already issue, do not issue
     - Add busy bit to each reg
     - Set in ID, cleated in WB
   
### WAW Hazard
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8ce5b5c7-fb5c-4a01-bba9-22768b7459e7)

### Practice Quiz
Why compilers or assembler programmers produce instructions with WAW hazards? Can we just assume that such instructions are never executed?
- Yes, because of branch delay slot, we may have an instruction that is useless for some branch paths

### RAW Hazards in Longer Pipelines
- Stalls due to RAW hazards are more frequent
  - Instruction reads register written by preceding instruction
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/4eed5a27-d586-419a-b359-d1b8b98668f5)

### Forwarding in Longer Pipelines
- Check if dest reg in EX/MEM (?), A4/MEM, M7/MEM, DIV/MEM, or MEM/WB pipeline regs is src reg of FP instr

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/713f2edd-3b7f-40e2-bb55-7e8a66f12a09)

# MIPS R4000 Pipeline
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/cff8420c-0dbd-4e2f-8a9c-7c8a8f94fbc7)

- IF: 1st half of instruction fetch
- IS: 2nd hald of instruction fetch
- RF: instruction decode, register fetch, instr cache hit detection
- EX: execute, add. calculation, branch target and condifiotn calculation
- DF: 1st half of data fetch
- DS: 2nd half of data fetch
- TC: tag check, 3rd half of data fetch
- WB: write back

# Code Examples and Pipeline Assumptions
### Basic Pipeline Scheduling: Example
```C
double x[1000], s;
for (i = 0; i < 1000; i++)
  x[i] = x[i] + s;
```
```
; R1 = x = &x[0]
; R2 = &x[1000]
; F2 = s
for: L.D   F0,0(R1)  ; F0 = x[i]
     ADD.D F4,F0,F2  ; F4 = x[i]+s
     S.D   F4,0(R1)  ; x[i] = F4
     DADDI R1,R1,8   ; R1 += 8 = &x[i+1]
     BNE   R1,R2,for ; if (R1 != &x[1000]) goto for
     NOP             ; branch delay slot
```

### Pipeline Assumptions
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2421a048-dfbd-4c5f-9871-12d5ed17e29f)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d800eb70-7fda-4bc6-8a2d-354ee3aba176)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/33558849-1681-4fc8-877d-8fb933963348)

(Assume that multiple instr can be in MEM or WB stage during the same cycle. Previously we assumed that they couldn't)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8563a328-33c9-4b8b-8db8-b04c882dc12d)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/10dd7c2f-f42f-4e74-aa05-87c33ddf3196)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b263c961-f872-4300-b524-d7fd2901caa1)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c2fc65ce-cb23-4e32-af82-340074fea740)

# Scheduling to Reduce Stalls
### How the Loop Will Be Executed
```
for: L.D   F0,0(R1)  
     ADD.D F4,F0,F2  
     S.D   F4,0(R1)
     DADDI R1,R1,8  
     BNE   R1,R2,for 
     NOP            
```
Will be executed as:
```
for: L.D   F0,0(R1)
     stall  ; Load to Any
     ADD.D F4,F0,F2
     stall  ; FP ALU to Store
     stall
     S.D   F4,0(R1)
     DADDI R1,R1,8
     stall  ; Integer to Branch
     BNE   R1,R2,for 
     NOP            
```
10 cc per iteration
- 4 stall cycles + branch delay slot

### Schedule Loop to Eliminate Stalls
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/efdcbe66-0fef-4245-b381-57733d29c21d)

6 cc per iteration but only 3 instrs do actual work

# Loop Unrolling
### Loop Unrolling
- Replicate loop body multiple times, adjusting loop termination code
  
  Unrolling 4 times:

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/23cab0ed-e626-4c01-a77d-8a6e5cb39ef2)

- Loop count n can be unknown or no multiple of loop unrolling factor k
- Then need 2 loops:
  - One unrolled that iterates n div k times (e.g. 7 div 3 = 2)
  - Copy of original that iterates n mod k times (e.g. 7 mod 3 = 1)
  - Unfortunately, div and mod operations are very expensive and should be avoided if possible

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d3bf01f1-1c76-462e-9cc2-6c36fcce946b)

### Unrolled Example Loop
```
for: L.D   F0,0(R1)
     ADD.D F4,F0,F2
     S.D   0(R1),F4
     DADDI R1,R1,8
     BNE   R1,R2,for
     NOP
```
Unrolled by a factor of 4:
```
for: L.D   F0,0(R1)
     ADD.D F4,F0,F2   ; 1 cycle stall
     S.D   0(R1),F4   ; 2 cycles stall

     L.D   F0,8(R1)
     ADD.D F4,F0,F2   ; 1 cycle stall
     S.D   8(R1),F4   ; 2 cycles stall

     L.D   F0,16(R1)
     ADD.D F4,F0,F2   ; 1 cycle stall
     S.D   16(R1),F4  ; 2 cycles stall

     L.D   F0,24(R1)
     ADD.D F4,F0,F2   ; 1 cycle stall
     S.D   24(R1),F4  ; 2 cycles stall

     DADDI R1,R1,#32
     BNE   R1,R2,for  ; 1 cycle stall
     NOP
```
We cannot move the second load right after the first because they are using the same registers. Thus, we need to use register renaming.

After register renaming:
```
for: L.D   F0,0(R1)
     ADD.D F4,F0,F2   ; 1 cycle stall
     S.D   0(R1),F4   ; 2 cycles stall

     L.D   F6,8(R1)
     ADD.D F8,F6,F2   ; 1 cycle stall
     S.D   8(R1),F8   ; 2 cycles stall

     L.D   F10,16(R1)
     ADD.D F12,F10,F2   ; 1 cycle stall
     S.D   16(R1),F12  ; 2 cycles stall

     L.D   F14,24(R1)
     ADD.D F16,F14,F2   ; 1 cycle stall
     S.D   24(R1),F16  ; 2 cycles stall

     DADDI R1,R1,#32
     BNE   R1,R2,for  ; 1 cycle stall
     NOP
```
Now we can reorder

Schedule unrolled loop to avoid stalls
```
for: L.D   F0,0(R1)
     L.D   F6,8(R1)
     L.D   F10,16(R1)
     L.D   F14,24(R1)
     ADD.D F4,F0,F2
     ADD.D F8,F6,F2
     ADD.D F12,F10,F2
     ADD.D F16,F14,F2
     S.D   0(R1),F4
     S.D   8(R1),F8     ; we cleared store stall, so can move onto DADDI
     DADDI R1,R1,#32
     S.D   -16(R1),F12  ; eliminate stall between DADDI and BNE
     BNE   R1,R2,for
     S.D   -8(R1),F16
```
- Runs in 14 cc (no stalls) per iteration
  - 14/4 = 3.5 cc per element
- Made possible by:
  - Movig all loads before all ADD.D
  - Moving 1 S.D between DADDI and BNE
  - Moving 1 S.D in branch delay slot
  - Using different registers
- When is it safe for compiler to do such changes?

### Compiler Steps
- Steps compilers perform to reschedule loop:
  - Determine that loop unrolling would be useful by finding that loop iterations were independent
  - Use different registers to avoid name dependencies
  - Eliminate extra test & branch instrs and adjust loop termination and iteration code
  - Determine that it is possible to move S.D after DADDI and BNE, and find amount to adjust S.D offset
  - Determine that loads and stores in unrolled loop can be interchanged by observing that loads and stores from different iterations are independent
    - Requires analyzing memory addresses to find that they do not refer to the same address
  - Schedule the code, preserving any dependencies needed to yield same result as original code
### Pros and Cons of Loop Unrolling
- Advantages:
  - Reduces loop overhead
  - Improves potential for instruction scheduling
- Disadvantages:
  - Increases code size
    - Concern in embedded domain
    - May increase istructon cache miss rate
  - Shortfall in registers
    - Register pressure
      
### Personal Exercise
Unrolling loop by factor of 3
```
; original loop
for: L.D   F0,0(R1)
     ADD.D F4,F0,F2
     S.D   0(R1),F4
     DADDI R1,R1,8
     BNE   R1,R2,for
     NOP
```
```
; unrolled 3 times
for: L.D   F0,0(R1)
     ADD.D F4,F0,F2
     S.D   0(R1),F4

     L.D   F0,8(R1)
     ADD.D F4,F0,F2
     S.D   8(R1),F4

     L.D   F0,16(R1)
     ADD.D F4,F0,F2
     S.D   16(R1),F4

     DADDI R1,R1,#24
     BNE   R1,R2,for
     NOP
```
```
; register renaming
for: L.D   F0,0(R1)
     ADD.D F4,F0,F2
     S.D   0(R1),F4

     L.D   F6,8(R1)
     ADD.D F8,F6,F2
     S.D   8(R1),F8

     L.D   F10,16(R1)
     ADD.D F12,F10,F2
     S.D   16(R1),F12

     DADDI R1,R1,#24
     BNE   R1,R2,for
     NOP
```
```
; avoid stalls
for: L.D   F0,0(R1)
     L.D   F6,8(R1)
     L.D   F10,16(R1)

     ADD.D F4,F0,F2
     ADD.D F8,F6,F2
     ADD.D F12,F10,F2

     S.D   0(R1),F4
     S.D   8(R1),F8

     DADDI R1,R1,#24
     S.D   -8(R1),F12
     BNE   R1,R2,for
     NOP
```
