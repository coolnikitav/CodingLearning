# LC3 Controller
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/6709a018-5cc2-4024-8da9-2f176df188a4)

## LC3 Behavior
- This project addresses ALU (ADD, NOT, AND) and Memory (LEA) operations. All of these instructions take 5 clock cycles
- LC3 is unpipelined. Each instruction goes through 5 cycles: Fetch -> Decode -> Execute -> Writeback -> UpdatePC
- This project does not address typical pipeline issues like control and data dependence

## Instruction Memory
- The instructions are stored, starting at address 3000
- After conducting additional research, I implemented instruction memory to store upto 4096 instructions
- The first 4 instructions are taken from the project example
  - @3000: 5020 (AND R0 R0 #0)
  - @3001: 1422 (ADD R2 R0 #2)
  - @3002: 1820 (ADD R1 R2 R0)
  - @3003: EC03 (LEA R6 #-2)
- The 4 example instructions will be follow be 21 randomized instructions.
