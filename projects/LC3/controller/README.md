# LC3 Controller
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/6709a018-5cc2-4024-8da9-2f176df188a4)

## LC3 Behavior
- This project addresses ALU (ADD, NOT, AND) and Memory (LEA) operations. All of these instructions take 5 clock cycles
- LC3 is unpipelined. Each instruction goes through 5 cycles: Fetch -> Decode -> Execute -> Writeback -> UpdatePC
- This project does not address typical pipeline issues like control and data dependence
- The purpose of this controller is to correctly fill the 8 registers in the writeback module. They will be checked during verification.

## Instruction Memory
- The instructions are stored, starting at address 3000
- Address 16'h3000 is 16'b0011_0000_0000_0000. Thus, 16 bits will be used for instruction memory.
- The first 4 instructions are taken from the project example
  - @3000: 5020 (AND R0 R0 #0)
  - @3001: 1422 (ADD R2 R0 #2)
  - @3002: 1820 (ADD R1 R2 R0)
  - @3003: EC03 (LEA R6 #-2)
- Instructions 16'h3004-16'h4095 will be filled up with randomized AND, ADD, NOT, LEA operations.
