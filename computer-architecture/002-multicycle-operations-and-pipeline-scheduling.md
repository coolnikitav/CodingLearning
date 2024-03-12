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
