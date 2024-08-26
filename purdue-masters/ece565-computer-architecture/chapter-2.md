# Chapter 2

## Module 2.1 Programmability, Implementability, and Compatibility

### Instruction Set Architecture (ISA)
![image](https://github.com/user-attachments/assets/bb357fdd-a954-4354-81fb-fbc8323e0a16)

### What is an ISA?
- Q: What is an ISA?
![image](https://github.com/user-attachments/assets/af284364-c973-495c-a89f-39da0ac79b34)

### RISC vs CISC Foreshadowing
- Q: What part of iron law does CISC improve? What part of iron law does RISC improve?
![image](https://github.com/user-attachments/assets/074d6232-c405-4b76-9e7f-cf8debad0f84)

### So you want to make an ISA?
- Q: What are characteristics of a good ISA?
![image](https://github.com/user-attachments/assets/6bf5ccea-117c-4b72-8ac3-98c4cf4c3763)

### Programmability
- Q: Who generates the code?
![image](https://github.com/user-attachments/assets/3aad3d9b-893a-4fde-8d4c-c5df7cee8832)

### Implementability
- Q: What are some classical high-performance designs features?
- Q: What are ISA features that make implementing high performance hard?
- Q: Can every ISA be implemented?
![image](https://github.com/user-attachments/assets/6be634d1-14bc-4920-81aa-e7ab0a53edae)

### Compatibility
![image](https://github.com/user-attachments/assets/f765bd88-f54f-40d6-b5f5-4c7463e2fd17)

### The Compatibility Trap
- Q: Explain what traps are.
![image](https://github.com/user-attachments/assets/a686a45a-5a89-4f3a-80b9-e29deec20833)

### The Compatibility Trap Door
![image](https://github.com/user-attachments/assets/079ddfa3-46ee-4bb5-8d72-d320238d60ab)

### Blocking the Compatibility Trap Door
- Q: Why can you not define unused instruction fields as don't cares? What is the solution to this problem?
![image](https://github.com/user-attachments/assets/99b84554-a487-4350-9a43-f20a11aa184d)
- A: Once you define them as don't cares, you can define them as anything else.

## Module 2.2 Aspects of ISAs: Operand models, Registers

### Aspects of ISAs
![image](https://github.com/user-attachments/assets/1a344143-eb0c-4fc4-8b68-0b33c8df7d36)

### The Sequential Model
![image](https://github.com/user-attachments/assets/b508a9cc-6226-4cc0-8b4c-6fb86f3bd04a)

### Format
- Q: What are the pros and cons of fixed length format? What about variable length?
![image](https://github.com/user-attachments/assets/98338ccf-bad2-4d49-8039-f5deb56047a0)

### Example: MIPS Format
![image](https://github.com/user-attachments/assets/74fcce32-c5d7-4a61-9dab-0418a20428cd)

### Operand Model: Memory Only
![image](https://github.com/user-attachments/assets/46e6c25c-301e-4f24-8dd5-8d115f444fbb)

### Operand Model: Accumulator
- Q: How would mem[A] = mem[B] + mem[C] look like with an accumulator?
![image](https://github.com/user-attachments/assets/e1a7cc0c-b059-4d55-bb8f-dfb996d1f19b)

### Operand Model: Stack
- Q: How would mem[A] = mem[B] + mem[C] look like with a stack?
![image](https://github.com/user-attachments/assets/b5d589e0-c990-45ce-b373-68681da356d9)

### Operand Model: Registers
- Q: How would mem[A] = mem[B] + mem[C] look like with general-purpose registers?
- Q: How would mem[A] = mem[B] + mem[C] look like with load-store?
![image](https://github.com/user-attachments/assets/6d08a40d-15d7-4d59-bebb-eb606bb229f2)
We will only perform operations on registers in load-store.

### Operand Model Pros and Cons
- Q: Rank the 4 models for statuc code size, data memory traffic, and cycles per instruction.
![image](https://github.com/user-attachments/assets/561a720e-e122-4893-b95f-807d423a9225)

### How Many Registers?
![image](https://github.com/user-attachments/assets/fe75a4f6-ccbc-4844-bec6-446b6e9f632c)

## Module 2.3 Aspects of ISAs: Virtual address size, addressing modes, endianness, control flow

### Virtual Address Size
![image](https://github.com/user-attachments/assets/997f8976-efa1-4e0f-8ff6-d59cda8fd769)

### Memory Addressing
- Q: What are the 8 addressing modes?
![image](https://github.com/user-attachments/assets/f10cbf4b-a7d0-4052-ae88-de7d1db052fa)

### Example: MIPS Addressing Modes
![image](https://github.com/user-attachments/assets/974e6b98-4ca1-4826-8ce6-63a2a3b7a049)

### Two Mode Addressing Issues
![image](https://github.com/user-attachments/assets/b33db5e9-406b-439e-8a73-92c7be1744df)
