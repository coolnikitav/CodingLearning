# LC3
![image](https://github.com/coolnikitav/learning/assets/30304422/28a4dc9e-65af-4c24-a04c-d40f763849bf)

![image](https://github.com/coolnikitav/learning/assets/30304422/d31ad4a9-4693-4286-ae73-3734d6f411ad)

## Test Plan
Instruction memory:
- 3000: 5020 (R0 <- R0 & 0) AND imm
- 3001: 2C20 (R6 <- DMem[3024] == 3008): LD
- 3002: 1422 (R2 <- R0 + 2): ADD imm with bypass_alu_1
- 3003: 1280 (R1 <- R2 + 0): ADD imm with bypass_alu_2
- 3004: C180 (JMP R6): JMP
- 3008: 967F (R3 <- ~R1): NOT
- 3009: 3600 (R3 -> DMem[300A]): ST with bypass_mem_2
- 300A: 1A83 (R5 <- R2 + R3): ADD reg
- 300B: A802 (R4 <- DMem[3010] = 0015): LDI
- 300C: 5B01 (R5 <- R4 & R1): AND reg with bypass_mem_1
- 300D: 0A04 (R5 != 0): BR to 3012
- 3012: 5CA4 (R6 <- R2 + 4): ADD imm
- 3013: (R7 <- DMem[LDR

Data memory:
- 300E: 3010
- 3010: 0015
- 3024: 3008
