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
