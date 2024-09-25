# Chapter 4

## Module 4.1 Motivation, Overview of Dynamic Scheduling

### The Problem With In-Order Pipelines
![image](https://github.com/user-attachments/assets/45002796-99c1-450f-abe7-ca5bef082fee)

### Dynamic Scheduling: The Big Picture
![image](https://github.com/user-attachments/assets/08c68665-6595-4b8c-a711-e26f64dc7260)

### Dynamic Scheduling - OOO Execution
![image](https://github.com/user-attachments/assets/56cc420b-983c-43dc-90c3-29fe79731da0)

## Module 4.2 Instruction Issue "Window": The Issue Queue

### Static Instruction Scheduling
![image](https://github.com/user-attachments/assets/6dd9c803-c39c-4844-8305-e8e716292d33)

### Motivation For Dynamic Scheduling
![image](https://github.com/user-attachments/assets/cfefe54a-4e5a-48aa-9e39-c20462f5673a)

### Before We Continue
![image](https://github.com/user-attachments/assets/00e8e364-9ecb-4700-b1e7-03f022cd96bb)

### Going Forward: What's Next
![image](https://github.com/user-attachments/assets/ed6927b3-8611-4eb7-8f67-e8ba84cbcac3)

### Dynamic Scheduling as Loop Unrolling
![image](https://github.com/user-attachments/assets/1e0be6e6-c606-427d-a31f-ef64c06fb25e)

### Loop Example: SAX (SAXPY - PY)
![image](https://github.com/user-attachments/assets/d0c5a183-c089-493c-97d1-6a7689e9d2fe)

### New Pipeline Terminology
![image](https://github.com/user-attachments/assets/a5762d8b-14d3-48f2-ab20-fd1603993261)

### New Pipeline Diagram
![image](https://github.com/user-attachments/assets/f53ecb9d-bc1b-4601-a3f6-0af9f1d5f6b7)

### The Problem With In-Order Pipelines
![image](https://github.com/user-attachments/assets/d01dc734-4377-423e-b481-ea0f7bcefd72)

### Issue Queue
![image](https://github.com/user-attachments/assets/9248d239-1696-42a4-8947-34e4b7a65228)

### Dispatch and Issue
![image](https://github.com/user-attachments/assets/fb540fa9-648b-4fa1-951a-390974445ef4)

### Dispatch and Issue with Floating Point
![image](https://github.com/user-attachments/assets/cf8077b2-8c30-4056-bd1a-1b1b8592a7ba)

## Module 4.3 Scoreboard

### Scheduling Algorithm 1: Scoreboard
![image](https://github.com/user-attachments/assets/cb18ea7e-f94d-48b5-9284-4d60f00e9046)

### Simple Scoreboard Data Structures
![image](https://github.com/user-attachments/assets/7808e560-72a9-4825-a634-7ec8eda30522)

### Scoreboard Data Structures
![image](https://github.com/user-attachments/assets/b91e36ce-5c55-47dc-9f01-a0db28baca05)

Cycle 1:

![image](https://github.com/user-attachments/assets/7d76857a-b864-4161-9959-5535457a0900)

Cycle 2:

![image](https://github.com/user-attachments/assets/30aeb42d-806a-42f9-927d-16ab0aa89764)

Cycle 3:

![image](https://github.com/user-attachments/assets/5a69004e-1b1d-4bde-bc1e-38f2fc8a2c19)

Cycle 4:

![image](https://github.com/user-attachments/assets/8d978d82-2025-459d-b8bc-b742fd3f5b40)

Cycle 5:

![image](https://github.com/user-attachments/assets/72a81c20-043d-4265-8a6f-22ed700e1eec)

Cycle 6:

![image](https://github.com/user-attachments/assets/c3d59617-4fab-409f-8f09-dbe931b23dac)

Cycle 7:

![image](https://github.com/user-attachments/assets/77f54520-c46f-411d-952e-907a817b64ba)

Cycle 8:

![image](https://github.com/user-attachments/assets/30bd812f-14ec-40ed-930e-9a8e8a764104)

Cycle 9:

![image](https://github.com/user-attachments/assets/77f76600-ab36-415d-87b2-54ac1ad89108)

Cycle 10:

![image](https://github.com/user-attachments/assets/148d986c-1482-4552-bb50-3172d350ed4e)

### In-Order vs. Scoreboard
![image](https://github.com/user-attachments/assets/e83174ef-59fc-4df8-b952-82242f3f7f4c)

### In-Order vs. Scoreboard 2: 5-cycle cache
![image](https://github.com/user-attachments/assets/20bdecad-722b-4b44-a9f7-51356f170b23)

## Module 4.4 Tomasulo's Scheduling

### Scoreboard Redux
![image](https://github.com/user-attachments/assets/e0e4f779-2498-46a3-8e1f-5f867bab9323)

### Register Renaming
- Q: How does register renaming work? What technique is used? What happens on a write and what happens on a read?

![image](https://github.com/user-attachments/assets/e5149eb8-65b8-4e92-aee0-9da790b5f0a2)

![image](https://github.com/user-attachments/assets/0611aaf3-657e-4fe3-b92c-9e7f9ccb1c80)

### Scheduling Algorithm 2: Tomasulo
![image](https://github.com/user-attachments/assets/379b463a-e127-458b-b27a-78619d32c606)

### Tomasulo Data Structures
![image](https://github.com/user-attachments/assets/5185d0fd-b2e2-46d1-885f-d80675642b51)

### Simple Tomasulo Data Structures
![image](https://github.com/user-attachments/assets/036ece0e-7063-4e23-96c3-29dbc8f1b5d5)

### Simple Tomasulo Pipeline
- Q: What are the stages in the Tomasulo pipeline?

![image](https://github.com/user-attachments/assets/02d61835-b005-4988-abbc-51d674d465c0)

### Tomasulo Dispatch (D)
![image](https://github.com/user-attachments/assets/199f82d9-9e23-4772-9c46-53a752b6c295)

### Tomasulo Issue (S)
![image](https://github.com/user-attachments/assets/7933ca50-3f84-44e5-b7c1-3b3b2e2a60ea)

### Tomasulo Execute (X)
![image](https://github.com/user-attachments/assets/004a77e0-d49d-44dd-ab6d-d2d880e65a22)

### Tomasulo Writeback (W)
![image](https://github.com/user-attachments/assets/b3e0e9a2-0873-4634-8e52-7fdf2c437fbe)

### Difference Between Scoreboard...
![image](https://github.com/user-attachments/assets/d0cfbd8f-4401-4366-b264-8e62218ccc05)

### ...And Tomasulo
![image](https://github.com/user-attachments/assets/1e2fb373-dc02-4b19-99ec-6fa67414f3b4)

### Value/Copy-Based Register Renaming
![image](https://github.com/user-attachments/assets/81077824-6c47-4b51-8f78-aea17eceb8b0)

### Value-Based Renaming Example
![image](https://github.com/user-attachments/assets/6a08b55c-58f7-429a-a3cc-030e5f88c613)

### Tomasulo Data Structures
- Q: Fill out these tables:

![image](https://github.com/user-attachments/assets/3ad3af70-63df-47c3-8a8d-940899f6c8db)

cycle 1:

![image](https://github.com/user-attachments/assets/7df0d57f-868f-4ae1-b3f3-34bfd05dbafb)

cycle 2:

![image](https://github.com/user-attachments/assets/9be951af-7f72-46ea-a2ec-ec82885217b5)

cycle 3:

![image](https://github.com/user-attachments/assets/db4728cb-77c8-451b-a4f4-63b75f8a1a03)

cycle 4:

![image](https://github.com/user-attachments/assets/92af3025-27fe-4177-adee-f0adb632d05c)

cycle 5:

![image](https://github.com/user-attachments/assets/7efc1fc2-6544-495b-a495-e80f6d0913cb)

cycle 6:

![image](https://github.com/user-attachments/assets/e9fe7f41-97f9-4cc0-acce-f7939c323efc)

cycle 7:

![image](https://github.com/user-attachments/assets/437d5a4a-1894-4ad2-aa13-67c7f58c3c3f)

cycle 8:

![image](https://github.com/user-attachments/assets/5abc7e6d-807e-468f-a7e4-f09b985c1a13)

cycle 9:

![image](https://github.com/user-attachments/assets/7a246d05-4b46-49b9-9d66-2ac8ca426a16)

cycle 10:

![image](https://github.com/user-attachments/assets/515e45b2-5f83-400b-be8b-33e331ee8354)

### Scoreboard vs. Tomasulo
![image](https://github.com/user-attachments/assets/2063361c-085e-4341-9e9e-05bc8e1cd48d)

### Scoreboard vs. Tomasulo 2: Cache
![image](https://github.com/user-attachments/assets/181a3905-e550-498c-b86b-78bd0c843d7b)

# Knowledge Check
- Q1: The issue queue logically separates the pipeline front end from the backend.
- Q2: The issue queue offers first-in-first-out semantics; hence the name "queue".
- Q3: Instructions enter the issue queue in program order.
- Q4: Instructions leave the issue queue after a fixed delay of N cycles where N depends on the pipeline depth.
- Q5: Register renaming eliminates all RAW and WAR hazards.
- Q6: In the Scoreboard issue queue, everytime a new register value is produced, all instructions that were waiting on that register value are notified via broadcast.
- Q7: The register status table in the Scoreboard tracks the functional unit that will produce the register values.
- Q8: Tomasulo's method renames registers by pointing register names to physical register locations.
- Q9: Register values are stored outside the architectural register file in Tomasulo's scheduling method.
- A1: True
- A2: False
- A3: True
- A4: False
- A5: False
- A6: True
- A7: True
- A8: False
- A9: True

## Module 4.5 Overview of Precise Interrupts and the Reorder Buffer

### This Unit: Dynamic Scheduling 2
![image](https://github.com/user-attachments/assets/ed7d77de-9f4f-4bb1-9ff9-3608de066441)

### Superscalar + Out-of-Order + Speculation
![image](https://github.com/user-attachments/assets/4b03347e-01dd-4721-9718-9a840b096d64)

### Speculation and Precise Interrupts
![image](https://github.com/user-attachments/assets/c197c7dc-2bdc-4b4b-a14e-7f9e4667d26e)

### Precise State
- Q: When you mispredict a branch, what do you do with younger instructions that have already completed?

![image](https://github.com/user-attachments/assets/4c0e6afc-df48-4fe2-b791-7a7f7a280d94)

### Precise State Options
![image](https://github.com/user-attachments/assets/5a42a506-01ab-477a-8f97-599be3025b79)

### The Problem With Precise State
![image](https://github.com/user-attachments/assets/de14e732-767f-43b3-b5da-89d4ed83e1f1)

### Jim Smith's Re-Order Buffer (ROB)
- Q1: What is RS on this slide?

![image](https://github.com/user-attachments/assets/609c1e90-8a0a-4d88-8c18-b46b96a1f21c)

- A1: Reservation stations.

### Complete and Retire
![image](https://github.com/user-attachments/assets/a3e20633-4bd3-4103-8b24-af5f77794eec)

### Load/Store Queue (LSQ)
![image](https://github.com/user-attachments/assets/a71cc43c-912e-4b80-b303-6006774e3eb4)

## Module 4.6 Memory Dependence and the Load/Store Queue

### ROB + LSQ
![image](https://github.com/user-attachments/assets/e877c27d-ad95-4cb7-860c-aea535c6f0c3)

### P6
- Q: Describe P6.
  
![image](https://github.com/user-attachments/assets/d78d66ad-4fe1-46fd-a810-d471704f131b)

### P6 Data Structures
![image](https://github.com/user-attachments/assets/6b5e3038-102f-4453-b73f-c93c9a4144f0)

### P6 (Tomasulo + ROB) Redux
![image](https://github.com/user-attachments/assets/dd921222-5ef3-42c1-bebe-a3d6a715caf4)

### The Problem with P6
![image](https://github.com/user-attachments/assets/280ba66d-a954-47a1-adb5-6cd880365b25)

## Module 4.7 The R10K Microarchitecture

### MIPS R10K: Alternative Implementation
![image](https://github.com/user-attachments/assets/51d19b8a-a661-4ba5-b588-90bfa9c34f06)

### Register Renaming in R10K
- Q: What does the number of physical registers equal to?
  
![image](https://github.com/user-attachments/assets/decf1239-c169-40f2-a274-9fccbca4f8de)

### Register Renaming Example
![image](https://github.com/user-attachments/assets/19264d42-e029-4295-b9ab-a68203ca10c5)

### Freeing Registers in R10K
- Q: What registers get freed when add retires, sub retires, mul, div:
![image](https://github.com/user-attachments/assets/d55f6a17-a895-4ac3-b1a9-afcc05c3ecb6)

![image](https://github.com/user-attachments/assets/bc7402fe-aca3-4d5d-bd5b-9fbde158bd53)

### R10K Pipeline
![image](https://github.com/user-attachments/assets/90c3617f-b1ab-4f9f-bf00-0721b92d92ba)

### R10K Dispatch (D)
![image](https://github.com/user-attachments/assets/f4490019-f2d2-46df-89c6-2dc7489f5597)

### R10K Complete (C)
![image](https://github.com/user-attachments/assets/49bd5407-543b-4e4c-81dd-bc6e2afc64d6)

### R10K Data Structures
- Q: Fill out the table.
  
![image](https://github.com/user-attachments/assets/556d9319-6285-4114-859b-adfe70d56af1)

### R10K: Cycle 1
![image](https://github.com/user-attachments/assets/ad7bb00b-999e-4b2e-8410-ed4da8e7974f)

+ means the value is already computed

### R10K: Cycle 2
![image](https://github.com/user-attachments/assets/e963f497-584d-4c45-8f33-76b69952c5ec)

### R10K: Cycle 3
![image](https://github.com/user-attachments/assets/9ee8d355-3ef4-431a-b1bc-060fced22888)

### R10K: Cycle 4
T and Told for store are empty because there were no registers to rename

![image](https://github.com/user-attachments/assets/dedfb4d7-2c25-4e33-8129-14ee42e83038)

### R10K: Cycle 5
![image](https://github.com/user-attachments/assets/d3213a34-bdc2-4e07-ad28-72add23c844c)

### Precise State in R10K
- Q: What are the 2 ways of restoring a state in R10K?
  
![image](https://github.com/user-attachments/assets/1c0ef976-f9ae-44be-ba02-1758ab882782)

## Module 4.8 Precise State Operation in the R10K Microarchitecture

### R10K: Cycle 5 (with precise state)
![image](https://github.com/user-attachments/assets/fde9015a-fb1d-42ab-a124-0fe7ce215d80)

### R10K: Cycle 6 (with precise state)
![image](https://github.com/user-attachments/assets/23fd242c-2b4d-4a55-8f25-b51e319ba261)

### R10K: Cycle 7 (with precise state)
![image](https://github.com/user-attachments/assets/2836643b-c995-409e-a266-5f17a0a04fba)

### R10K: Cycle 8 (with precise state)
- Q1: How is D$ write undone?

![image](https://github.com/user-attachments/assets/a0770e28-3c4d-466c-ad14-8fc480bd9f84)

- A1: Nothing ever made it to memory because we were in a speculative state.

## Module 4.9 Out-of-Order Memory Operations

### Out of Order Memory Operations
![image](https://github.com/user-attachments/assets/209cb0c6-f469-4bcd-b08c-fd565261fee6)

### Data Memory Functional Unit
![image](https://github.com/user-attachments/assets/b2b204c0-b09d-4546-8459-f9c22206781a)

### Simple Data Memory FU: D$/TLB + SQ
![image](https://github.com/user-attachments/assets/14ec8f99-eeb9-4573-9cae-ab939b2c995b)

### Data Memory FU "Pipeline"
![image](https://github.com/user-attachments/assets/3432f77a-4f20-4f3e-a137-5a1bd56be81a)

### "Out-of-Order" Load Execution
![image](https://github.com/user-attachments/assets/2a187a81-2923-49eb-bee6-3bc077a4c8e4)

CAM - content addressable memory, FA$ - fully associative cache

### Conservative Load Scheduling
![image](https://github.com/user-attachments/assets/5ac77f5c-81df-47f3-abc4-52cb210f3860)

### Opportunistic Memory Scheduling
![image](https://github.com/user-attachments/assets/20e115b8-cefb-40e1-a085-3e2905f92c21)

### D$/TLB + SQ + LQ
![image](https://github.com/user-attachments/assets/fe3cf573-57e7-43cd-95b1-867abef175d5)

### Advanced Memory "Pipeline" (LQ Only)
![image](https://github.com/user-attachments/assets/5732e1c2-9787-4c2a-a315-ae115c6a13be)

### Detecting Memory Ordering Violations
![image](https://github.com/user-attachments/assets/5faed9f8-a274-4803-9bc2-e7d3328f6c57)

## Module 4.10 Intelligent Load Scheduling

### Intelligent Load Scheduling
![image](https://github.com/user-attachments/assets/0a768b81-c706-48aa-9c4a-fb25d9f10eac)

### Memory Dependence Prediction
![image](https://github.com/user-attachments/assets/c7f2a0f4-0687-4283-91c9-4e35fca26fbd)

