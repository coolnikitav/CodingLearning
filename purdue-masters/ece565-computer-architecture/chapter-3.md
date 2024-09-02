# Chapter 3

## Module 3.1 Understanding the Operation and Performance of Simple Pipelines

### Next: Baby Pipelining
![image](https://github.com/user-attachments/assets/502b234c-af3b-4239-a82f-2ca5b4d18997)

### Quick Review
![image](https://github.com/user-attachments/assets/f0126fd1-fa43-410b-a85a-3d186a40bdc5)

### Pipelining
![image](https://github.com/user-attachments/assets/b46fb83f-8175-4a44-9406-36dd8338185e)

### 5 Stage Pipelined Datapath
- Q: Why is PC not latched after ALU stage?
  
![image](https://github.com/user-attachments/assets/b9f10041-d289-4d14-99ac-b97377cc2055)

- A: PC is needed for branch instructions. The calculation will not be needed after the ALU stage.

### Pipeline Terminology
![image](https://github.com/user-attachments/assets/79c2d1d3-3571-43f3-a883-a67f7ece0b6b)

### Pipeline Control
![image](https://github.com/user-attachments/assets/63f15b59-369f-4bc6-9517-3c087dfed6be)

### Abstract Pipeline
![image](https://github.com/user-attachments/assets/abc4cf45-0883-4df2-9a77-efe6114b7e27)

### Floating Point Pipelines
![image](https://github.com/user-attachments/assets/90002237-f2a2-418e-b23b-588d70ef635d)

### Pipeline Diagram
![image](https://github.com/user-attachments/assets/6cff796c-d5bc-4cc7-9d47-5433fbcc4e83)

### Pipeline Performance Calculation
![image](https://github.com/user-attachments/assets/05f7af4f-2b01-492c-b974-f9a874cebe2d)

### Principles of Pipelining
![image](https://github.com/user-attachments/assets/0fc7c52d-6daa-4169-b808-b1e211e5298c)

### No, Part 1: Pipeline Overhead
- Q: Why does pipelining add extra delays?

![image](https://github.com/user-attachments/assets/97f1073d-b523-41d5-8e01-165d18fafe59)

### No, Part 2: Hazards
![image](https://github.com/user-attachments/assets/88275216-d8e8-497d-9e47-31cfd4f61dcd)

### Clock Rate vs IPC
![image](https://github.com/user-attachments/assets/055ee11f-41fb-44fc-8485-bb7a16c80914)

### Optimizing Pipeline Depth
- Q: What are the equations for IPC and freq in terms of gate delay, overhead per stage, and average stall per instruction per stage
  
![image](https://github.com/user-attachments/assets/f2198289-4c48-471c-bc11-c349b063c69d)
