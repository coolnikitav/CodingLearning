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
  - # slots per VLIW changes
  - # of parallel FUs changes
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
