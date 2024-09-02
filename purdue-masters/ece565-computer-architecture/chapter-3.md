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

## Module 3.2 Pipeline Hazards: Structural Hazards and Read-After-Write (RAW) Data Hazards

### Managing a Pipeline
![image](https://github.com/user-attachments/assets/798ce85b-c571-4d60-b843-a39dd0f30a8d)

### Structural Hazards
![image](https://github.com/user-attachments/assets/66cdb72e-94c8-41af-bea1-8198cc66fd9d)

### Fixing Structural Hazards
![image](https://github.com/user-attachments/assets/eac5fed3-daf4-4d9d-bfef-c89b926ec62d)

### Avoiding Structural Hazards (PRS)
- Q: What are the 3 ways mentioned to deal with structural hazards?

![image](https://github.com/user-attachments/assets/d02e696d-113a-4ee8-b586-73809c8b8da0)

### Data Hazards
![image](https://github.com/user-attachments/assets/19f4dd77-1416-469f-92d0-1ac3b9e91ec5)

### Dependences and Loops
![image](https://github.com/user-attachments/assets/01a9d0da-5b2f-486b-9fb3-b4e39c4f7d5b)

### RAW
![image](https://github.com/user-attachments/assets/b49f588d-59c0-4d91-97b2-c75ca98d246e)

### RAW: Detect and Stall
![image](https://github.com/user-attachments/assets/29d0b58d-75c6-47c1-8b09-821134cbaab1)

### Two Stall Timings (without bypassing)
![image](https://github.com/user-attachments/assets/41b1cbc0-5695-48b9-8b9b-df9fb2824447)

### Reducing RAW Stalls with Bypassing
![image](https://github.com/user-attachments/assets/4bba0b84-c56f-48b7-a8d8-3d11baa4bba2)

### Bypass Logic
![image](https://github.com/user-attachments/assets/e9be6b1b-4e1d-43bd-95f3-88ed459bd991)

### Pipeline Diagrams with Bypassing
![image](https://github.com/user-attachments/assets/a4137076-714d-439f-98db-03c64915cfe3)

### Load-Use Stalls
![image](https://github.com/user-attachments/assets/1ace2ec9-7950-4e34-aed3-127c42c0cfb8)
