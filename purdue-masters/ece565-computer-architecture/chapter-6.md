# Chapter 6

## Module 6.1 Thread-Level Parallelism (TLP) and Data-level Parallelism (DLP)
![image](https://github.com/user-attachments/assets/6e993df8-ac01-4df3-8217-9248ff83d030)

### Parallelism in Software
![image](https://github.com/user-attachments/assets/ad487f21-9661-4b43-ae96-98c7b7f9308a)

### Thread Level Parallelsim (TLP)
![image](https://github.com/user-attachments/assets/0b33c4c8-6937-4383-9a5c-532e54023740)

### One Thread Per Core?
![image](https://github.com/user-attachments/assets/2ecec935-30d0-4d42-ba46-d509d3927668)

### Hardware Idle Due to Memory Latency
![image](https://github.com/user-attachments/assets/0a4ace02-4b3a-4f23-a780-a6761dbc1170)

### Hardware Multithreading?
![image](https://github.com/user-attachments/assets/fce3dea8-e080-4e26-8c49-f131d4071683)

### Fine-Grained Multithreading
![image](https://github.com/user-attachments/assets/92cabd23-eefe-441a-8316-9d569bd8a24d)

![image](https://github.com/user-attachments/assets/a0b22a2d-9d8e-470f-9f13-09f69ad2eb62)

### Simultaneous Multithreading
- Q: Explain superscalar vs coarse grained vs fine grained vs smt. Remember the time vs execute slots graph with threads on it.

![image](https://github.com/user-attachments/assets/d51ce821-c5aa-4ae8-9ffd-24c753d51a8e)

## Module 6.2 DLP, Vector Computing, Overview of GPUs

### Data Level Parallelism (DLP)
![image](https://github.com/user-attachments/assets/7501d348-ed05-4f16-a422-738fdcc46c64)

### Vector vs. ILP - Why do vector?
![image](https://github.com/user-attachments/assets/bd703f15-7a3f-40fa-a3d8-47ae6db27dfc)

### HW simplifications because of Vector
- Q: Why can pipelines be deeper with vectors?

![image](https://github.com/user-attachments/assets/dc785aeb-a00f-454a-b320-2be6729391d9)

### Vector Sizing
![image](https://github.com/user-attachments/assets/17e26c2b-f860-4b5f-96c6-a55d20dd3970)

### Strip Mining
![image](https://github.com/user-attachments/assets/86849bc7-b43e-418b-a934-8548013d8ec4)

### Strip Mining Example
- Q: Convert the following code to pseudo-assembly vector code:![image](https://github.com/user-attachments/assets/b6033ef6-7770-4772-87ca-6813c76c81e2)

![image](https://github.com/user-attachments/assets/9a6f68f9-fc38-45d2-b81a-8e4d65f96e44)

### Vectors wider than SIMD width
![image](https://github.com/user-attachments/assets/5700e466-5e81-4387-9ae4-bcc05f03b7e1)

### Vector Functional Unit Layout
![image](https://github.com/user-attachments/assets/3f620d28-8d3f-45cf-933c-ff7567f36ef7)

### Vector Memory Operations
- Q: What does unit stride mean?
  
![image](https://github.com/user-attachments/assets/92f26e3e-6b77-439f-894e-f54ecdfb4294)

- Q: How would non-unit stride and scatter/gather be different?

![image](https://github.com/user-attachments/assets/75509d8a-01bf-4d4b-b9bf-d302efba3ff7)

### Vector Accessing Memory
- Q: Write assembly code for this: ![image](https://github.com/user-attachments/assets/25d6ef85-0aef-4266-8942-4e293f3ab05a)

![image](https://github.com/user-attachments/assets/83796b1e-c2b4-430f-a824-db28003101fd)

### Handling Conditional Operations In A Loop
- Q: Write this code in assembly:![image](https://github.com/user-attachments/assets/a433e7f6-4024-4e64-ac97-aa2d8b6d8c52)

![image](https://github.com/user-attachments/assets/152e8095-d143-4cf0-8cfe-294257185eac)

### Intel x86 (MMX, SSE, AVX) vs Vector Machine
![image](https://github.com/user-attachments/assets/d6fc5f06-d690-4476-88fa-46a45b99a389)

![image](https://github.com/user-attachments/assets/775d9dbe-a6aa-4802-9fd7-0d9f0dbf8c8d)

### Vectors and Super Computers
![image](https://github.com/user-attachments/assets/25375e2d-54d4-4d1c-8b44-1763f0bcb159)

### What is a GPU?
![image](https://github.com/user-attachments/assets/6e03fdca-f43d-4b52-985c-9485422045c1)

### Graphics Processing Units (GPUs)
![image](https://github.com/user-attachments/assets/514f5592-053e-423d-b3c3-015f2481fd54)

### The GPU is Ubiquitous
![image](https://github.com/user-attachments/assets/8da7bf9b-6b4a-49a0-9b78-a5a4b1a9d203)

### Why use a GPU for computing?
![image](https://github.com/user-attachments/assets/83eac2d1-093e-4a14-8b5e-65f2994dad08)

### GPU uses larger fraction of silicon for computation than CPU?
![image](https://github.com/user-attachments/assets/18d0cf9a-613b-40d3-8f1e-9e40dfed6a10)

### GPGPUs vs Vector Processors
![image](https://github.com/user-attachments/assets/2239e081-12a0-4143-a45a-03610154713e)
