# LC3 Controller
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/6709a018-5cc2-4024-8da9-2f176df188a4)

## LC3 Behavior
- This project addresses ALU (ADD, NOT, AND) and Memory (LEA) operations. All of these instructions take 5 clock cycles
- LC3 is unpipelined. Each instruction goes through 5 cycles: Fetch -> Decode -> Execute -> Writeback -> UpdatePC
- This project does not address typical pipeline issues like control and data dependence.
