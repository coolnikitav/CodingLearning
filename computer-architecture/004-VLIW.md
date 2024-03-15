# Basic VLIW Approach
### Basic VLIW Approach
- Multiple independent FUs
- Operations executed in parallel on these FUs packed into 1 VLIW
  - Group of operations that are executed in parallel
  - 1 instruction, multiple concurrent operations
  - Unused operation slots need to be filled with NOPs
- Example instruction for VLIW processor with 2 LD/ST units (LSUs), 2 FP unites, 1 integer/branch unit:
  
  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c4a60839-1015-4562-bb03-033651ca342c)

### Example Pipelined VLIW Processor
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/929f830d-5e1b-43ae-ba38-892bfdcbcbbf)

- No dependency checking HW
  - Done by compiler
- Issuing ops to FUs easy
  - Ops aligned with FUs
- Many register file ports
  - Superscalar also
- Fetching parallel ops easy

### VLIW vs Superscalar
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2d9d26a8-b3cc-4e02-8aca-f54c06a1155e)

### VLIW Code Example
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e9184c5f-5641-4e3f-8e49-388f57300319)

Assignment: unroll as many times as necessary to eliminate any stalls. Ignore delayed branches

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b10b3f23-eb3c-4a7b-99f1-d2b4ce1f75cf)

### VLIW Advantages, Disadvantages, Challenges
Advantages compares to superscalar
- Simpler (in principle) -> less hardware (but some complex design issues)
- Lower power consumption

Disadvantages compared to superscalar
- Binary incompatibility (in principle) -> programs must be recompiled when
  - #of slots per VLIW changes
  - #of of parallel FUs changes
  - perhaps even when op latency changes
- Very good compiler support needed

Challenges
- Scheduling for non-unit assumed latency
- Large code size
- Many-ported register file and complex forwarding logic
- Control hazards due to branches
- Lockstep operation: if one operation slot stalls, entire processor is stalled

### Exercises
What will be the efficiency of the VLIW code example if the loop is unrolled 8 times? Can 100% efficiency be obtained? Explain why/why not.
- We would produce 8 results in 9 cc, which is 9/8 = 1.125 result per cc.

# VLIW Challenges: Instruction Scheduling & Code Size
### VLIW Challenges and Potential Solutions
- Scheduling for NUAL (non unit assumed latency)
- Large code size
- RF (register file) complexity
- Control hazards

### UAL vs NUAL
Unit Assumed Latency (UAL)
- Program semantics: each instr completes before next one is issued
- Equals to conventional sequential model

Non-unit assumed latency (NUAL):
- more than 1 operation has non-unit latency L > 1
- Program semantics: exactly the next L-1 instrs are understood to have issued before this op completes
- Result observation delayed by L cycles

### NUAL Example
- Assumptions:
  - 5-stage pipeline
  - without forwarding
  - RF read in 2nd half of cc, RF write in 1st half
 
  UAL add has latency of 1, NUAL (VLIW) add has latency of 3:

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/4aea1c97-a06a-45fe-82b4-bb4b0324c371)

### NUAL Scheduling Models
"Equals (EQ)" Model
- Each operation takes exactly specified latency
  - dest reg will not be written until specified latency expires
- May work if latency fixed, but load latency difficult to predict (D$ hit?)
- Decreases register pressure
- Heavy requirements on exception model

"Less-Than-or-Equals (LEQ)" Model
- Operation may take  to specified latency
  - Dest reg can be written any time from issue to specified latency
- Simplifies implementation of precise exceptions
- Enables binary compatibility when latencies are reduced

### Large Code Size
- VLIWs are very long
  - Compiler cannot always fill all available issue slots:
    ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/49fd84e8-16f7-4e05-92d0-42230c649a6d)
- Variable length/compressed formats necessary to avoid excessive code size
- Compiler performs loop unrolling extensively to find independent operations leading to large instruction footprints

### Compact Encoding
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/cbe4c57c-022d-4dfc-aa44-583b5cb1d686)

### Mask-Based Encoding
- Add mask-bits to VLIW instructions
  - Mask indicates "what goes where" in instruction buffer
  - Mask also identifies next PC

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ea5ecc6f-1dfb-4611-8d5a-791e87dbc4a2)

### When to Decompress?
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/dfb3e4aa-bc88-4252-8585-1e4a175fa76c)

# VLIW Challenges: Register File Complexity & Control Hazards
### Register File Complexity
- Multiported register file
  - VLIW with 4 execution units (2-input, 1-output)
  - Need to read 8 and write 4 registers per cycle
  - N execution units -> 2N read ports / N write ports

    ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/cf45188a-047f-4a74-8002-1b7fbf551f9a)

- Register file are grows with square of number of ports
- Read access time grows linearly with number of ports
- What is reasonable today?
  - Depends on technology, in 0.18u:
    - Max: 15-20 ports (read and write)
    - Sweet spot: around 12 ports (8-read, 4 write)
  - 15-20 ports can support 5-7 execution units
    - with simultaneous operand accesses

### Clustered VLIW
- Partition the register file
  - Each register file connected to a few execution units
    - In today's technology, > 1 execution unit per register file
- Different clustering models available
  - Explicit copy: normal ops can only access RF within cluster. For communication between clusters, explicit copy ops needed

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d20c2028-52ca-450a-9c3c-4ad623c83a31)

### Effects of Clustering on Performance
- Media-oriented integer benchmarks
- Multiflow VLIW compiler
- 16u/2c = 16 units, 2 clusters
- speedup over 1 unit, 1 cluster

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0b4a3295-7345-4175-aad3-a4fcad9e6697)

### Control Hazards
- Mispredicted branches break the pipeline
  - 5 cycle penalty in example 7-stage pipeline, larger for longer pipelines
  - Branch prediction decreases misprediction probability
  - Superscalars speculatively execute on predicted path
- What about VLIW processors?
  - Note: exposing delay slots as in MIPS is considered a bad idea...
 
  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1a70a789-edd7-4873-bf50-101eee8cd206)

### Unbundling Branches
- Unbundle branch in its basic components:
  - Whether (compare)
  - Where (compute branch target)
  - When (branch)
  - Expose latencies to compiler
- Compiler can move branch preparation earlier in instruction stream
- Increases code size, issue pressure, cache footprint,...

### 2-step Branching
- Comparison saved in "branch condition" register
- Can have few branch condition registers
  - to start preparing multiple branches
- Compare can be moved earlier by compiler
  - delay between compare and branch can be filled with other useful ops
- Branching still requires branch target address computation

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/634df59b-f837-4d03-99c9-f9f1ef07d629)

### Predication
- Conditional execution of operations based on Boolean guard

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8f9f4213-3f05-4210-aeb3-357626078332)
- Converts control dependencies -> data dependencies
  - Enlarges scheduling scope

  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/271808fc-0064-4989-bf50-a2cd6a9084d3)
