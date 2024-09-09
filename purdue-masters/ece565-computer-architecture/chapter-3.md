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

## Module 3.3 Compiler Scheduling for RAW Hazards
### Compiler Scheduling
![image](https://github.com/user-attachments/assets/dcba8f58-5439-4e04-ac4a-b874d0467c11)

### Compiling Scheduling Requires
![image](https://github.com/user-attachments/assets/7771c843-8342-4c2c-bb93-b6040f2d95c7)

![image](https://github.com/user-attachments/assets/3b7b5e80-84b0-4119-a658-9370478c5001)

![image](https://github.com/user-attachments/assets/3b9e46f2-33b5-466b-9ff7-fe9c9ce2b5ec)

## Module 3.4 WAR and WAW Hazards
### WAW Hazards
![image](https://github.com/user-attachments/assets/ab01644c-5fcb-4ba7-8df7-09bb5db51818)

### Handling WAW Hazards
![image](https://github.com/user-attachments/assets/2a67b03b-01c3-4d08-ad66-550fdfd29aca)

### Handling Interrupts/Exceptions
- Q: What is an example of interrupts? What about exceptions?
- Q: Explain precise state or precise interrupts

![image](https://github.com/user-attachments/assets/f04144fc-1982-4ce9-a80d-0874c501fd48)

### Handling Interrupts
![image](https://github.com/user-attachments/assets/f4876dae-d1e3-4906-923c-7300c2740cbf)

### More Interrupt Nastiness
![image](https://github.com/user-attachments/assets/9a62b675-682f-43ba-8f5b-4055258f783f)

### WAR Hazards
![image](https://github.com/user-attachments/assets/55eb92e1-4ed3-4ab2-b850-482da9824fc5)

### Memory Data Hazards
![image](https://github.com/user-attachments/assets/f395710e-d3e8-4fbe-9d8a-ef482d569a94)

## Module 3.6 Dynamic Branch Prediction: BTB and RAS
### Branch Resolution in our Simple Pipeline
![image](https://github.com/user-attachments/assets/2f3298dd-5914-4a0b-b314-09829dee5d08)

### Control Hazards
- Q: What is the CPI if branch is 20% of the intructions, 75% of branches are taken, and branches cause a 2 cycle stall?
  
![image](https://github.com/user-attachments/assets/761cbfd6-4527-4b40-a98d-b6bfdd179a87)

### ISA Branch Techniques
![image](https://github.com/user-attachments/assets/61b17cf8-932f-4643-9f01-5c0ab064a08d)

### Can We Do Better?
![image](https://github.com/user-attachments/assets/abd8f226-0131-4b74-b458-004ab26729f2)

### Predict Not Taken
![image](https://github.com/user-attachments/assets/e8a1d708-d129-439f-aef8-5ef74ba1060b)

### Big Idea: Speculation
![image](https://github.com/user-attachments/assets/208280b8-13ac-4d7f-ab02-474141eaeadb)

### Control Hazards: Control Speculation
![image](https://github.com/user-attachments/assets/b83f905c-bd8b-41f9-ab13-c5deef27e490)

### Control Speculation and Recovery
- Q: How to handle mis-speculation in an in-order pipeline?

![image](https://github.com/user-attachments/assets/58957439-9bc6-48b9-a6a1-39ea3728fa85)

### Dynamic Branch Prediction - take solution 3 further
![image](https://github.com/user-attachments/assets/41cdeceb-297b-4dd2-bf2f-434e458d7af6)

![image](https://github.com/user-attachments/assets/0fa7c9b8-1134-41e4-a416-da30a3c84edd)

### Hazards in Real Microprocessors
![image](https://github.com/user-attachments/assets/c25f6909-3283-4b45-86ea-e67fe2e44775)

### Dynamic Branch Prediction
![image](https://github.com/user-attachments/assets/04ed5f73-54fc-40cb-9e4c-0141db5cd398)

### Branch Prediction (I): Branch Target Buffer
![image](https://github.com/user-attachments/assets/42100bf9-27df-441c-a494-c818811cfab6)

![image](https://github.com/user-attachments/assets/dc39e5c4-0adf-4bd0-a9eb-2438369a9b28)

### Branch Target Buffer
![image](https://github.com/user-attachments/assets/04e2271c-16a4-4fc2-9ee0-c182673a0863)

### Why Does a BTB Work?
![image](https://github.com/user-attachments/assets/28aed2b8-8775-46a7-a80f-adf19c517893)

### Return Address Stack (RAS)
![image](https://github.com/user-attachments/assets/3e4cc95a-2b45-436e-93a8-a7aa73926388)
