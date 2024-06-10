# LC3
![image](https://github.com/coolnikitav/learning/assets/30304422/28a4dc9e-65af-4c24-a04c-d40f763849bf)

![image](https://github.com/coolnikitav/learning/assets/30304422/d31ad4a9-4693-4286-ae73-3734d6f411ad)

## Test Plan
Instruction memory:
- 3000: 5020 (R0 <- R0 & 0) AND
- 3001: 1422 (R2 <- R0 + 2): ADD with bypass_alu_1
- 3002: 1280 (R1 <- R2 + 0): ADD with bypass_alu_2
- 3003: 2C20 (R6 <- DMem[3024]): LD
- 3004: C180 (JMP R6): JMP
- 3008: 967F (R3 <- ~R1): NOT
- 3009: 3600 (R3 -> DMem[300A]): ST with bypass_mem_2

Data memory:
- 3024: 3008
