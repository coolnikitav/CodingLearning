# LC3 Fetch
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/82175d80-1c0a-4173-820a-db14d753a0e8)

### Inputs:
- clock
- reset
- enable_updatePC
- enable_fetch
- taddr
- br_taken

### Outputs:
- npc
- pc
- Imem_rd

### LC3 Behavior:
- On reset: pc = 3000, npc = 3001
- If br_taken = 1, PC = taddr, else PC = PC+1
- PC, npc, Imem_rd update only when enable_updatePC = 1
- If enable_fetch = 1, then set Imem_rd = 1 asynchronously else Imem_rd = Z (High impedance)

### Wiring diagram:
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7009913a-58ec-4242-8ea4-00645b7a1725)
