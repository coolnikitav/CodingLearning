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

### Control Flow Instructions
- Q: What are the 3 options we have when testing for conditions?
- Q: Explain their pros and cons.
![image](https://github.com/user-attachments/assets/7bd21abf-0c5f-48a0-8604-67a560115750)

### Example: MIPS Conditional Branches
![image](https://github.com/user-attachments/assets/fce3c8f9-065a-4c70-82bf-6edb56f496b5)

### Control Instructions II
- Q: Explain the 3 ways of computing targets.
- Q: What is each of these modes used for?
![image](https://github.com/user-attachments/assets/a98843fa-c86b-4d6b-870d-9205b4acced4)

### MIPS Control Instructions
![image](https://github.com/user-attachments/assets/9fc15a7c-74b7-4d16-90a8-4d5ad92108cd)

### Control Instructions III
![image](https://github.com/user-attachments/assets/c382a1a6-915d-4004-a256-8751ff09027c)

### RISC & CISC
![image](https://github.com/user-attachments/assets/decf6154-ebb9-4bbf-a1d5-c6e9a820314c)

## Module 2.4 Survey of ISAs in the Field
### Current Winner (units sold): RISC: ARM
![image](https://github.com/user-attachments/assets/dbb0f9d7-7a2a-4cfd-a21d-6e7733fe4cef)

![image](https://github.com/user-attachments/assets/1642bd6f-6691-426d-81a4-dd1847dcaa0f)

![image](https://github.com/user-attachments/assets/12538b8e-d16d-4f48-ae0d-5a78a438e78b)

### The ARM Business Model
![image](https://github.com/user-attachments/assets/e4a4aeb1-665f-46ea-801e-9f3e28037ed3)

### Historical Winner (revenue): x86
![image](https://github.com/user-attachments/assets/d52cfeed-204b-49a5-a563-e59dca0a811c)

### x86: Registers
![image](https://github.com/user-attachments/assets/ad062be7-4992-4d36-8007-585112d933b8)

### x86 Addressing
![image](https://github.com/user-attachments/assets/1fe26276-f372-4f57-a9b5-f1687b36af64)

### x86 Instruction Formats
![image](https://github.com/user-attachments/assets/9cc45d7f-1048-4587-90a9-1cc704ddada0)

### x86 Outside = RISC Inside
![image](https://github.com/user-attachments/assets/5ddb322c-e2da-4d1c-9fc6-45d6b65d3ba7)

### Transmeta's Take: Code Morphing
![image](https://github.com/user-attachments/assets/9fa98d06-85ff-4411-8366-4dbcb4f0f5a0)

### Emulation/Binary Translation
![image](https://github.com/user-attachments/assets/9a527608-8a0b-4f30-b397-c3bf13cf4422)

### Virtual ISAs
![image](https://github.com/user-attachments/assets/de168500-777a-4c51-83c4-d4a621cf1fbd)

## Module 2.5 Translating High-Level Code to MIPS Assembly
### Branches and Jumps
- Q: Convert the following code into assembly:
```
while(i != j) {
  j = j + i;
  i = i + 1;
}
```
![image](https://github.com/user-attachments/assets/1ef8b9a0-6d59-4c71-a6b5-621bac860da8)

![image](https://github.com/user-attachments/assets/f890163f-e082-4914-872c-05afc3df4d73)

![image](https://github.com/user-attachments/assets/6b2b1598-0698-49df-a65c-af8706c7bcf7)

### Assembly Exercise
![image](https://github.com/user-attachments/assets/3c562298-9fe3-4ba6-b9f7-520f12714e5d)

Ind stands for induction

![image](https://github.com/user-attachments/assets/5f59e414-7b04-478c-9807-d06169faa832)

### Procedure Calls
- Q: Explain the stack for the procedure calls. How do push and pop work?
  
![image](https://github.com/user-attachments/assets/c50c9616-5ccb-4a85-914a-4c5a5bc0545f)

![image](https://github.com/user-attachments/assets/7ad1a7ed-38b3-4526-a298-45aac9eaadce)
