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
