# LC3 Decode
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f87f99cf-a0c2-413b-a424-e54bce9fdd04)

### Inputs
- clock
- reset
- npc_in
- enable_decode
- IMem_dout

### Outputs
- IR
- npc_out
- W_Control
- E_Control
- Mem_Control

### LC3 Decode Behavior
- On reset, all outputs go to logic 0
- IR (instruction register) is equal to Instr_dout
- npc_out is equal to npc_in (passing to execute unit)
- enable_decode is the master enable

### W_Control
W_Control signal is a function of IR[15:12]. I focus only on ALU and LEA instructions and hence W_Controll is either 0 (ALU) or 2 (LEA). The full table of values is shown below:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/40a2bb9c-5580-4b2b-824f-1b5f7e2f35ba)

It is an ALU operation if IR[13:12] == 2'b01:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b4081918-52b9-41ce-955e-671ac5e9fa21)

It is an LEA operation if IR[15:12] == 4'b1110:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3b2d3afa-338d-47b2-81aa-7d3dff2c3a37)

### E_Control

### Wiring Diagram
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3fb97ea6-a669-485c-819b-0f3335a9b292)
