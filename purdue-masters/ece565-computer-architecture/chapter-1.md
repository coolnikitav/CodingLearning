# Chapter 1

## Module 1.3 Understanding Performance, Averaging, Benchmarks

### Performance Improvement
- Q: What can "Processor A is X times faster than processor B" mean?
  
![image](https://github.com/user-attachments/assets/5d0c383e-9c67-4429-b3c3-b247a90c4ffb)

### What is 'P' in Latency(P,A)?
![image](https://github.com/user-attachments/assets/bcd5c32c-b74e-429c-8c23-47b7a49364ca)

### SPEC Benchmarks
![image](https://github.com/user-attachments/assets/70e05208-7a2c-49c4-be85-cee51db1f3ac)

### SPEC Benchmark Evolution
![image](https://github.com/user-attachments/assets/5ee2ab52-16d4-4754-8a76-17f9cbc4d75c)

### Other Benchmarks
![image](https://github.com/user-attachments/assets/59116bb5-513e-4f3c-baed-1cd47964a47f)

### Adding/Averaging Performance Numbers
- Q: If we go 1 mile @ 30 miles/hour and 1 mile @ 90 miles/hour, what is the average speed?
  
![image](https://github.com/user-attachments/assets/860d46aa-973b-430f-bf06-5598083cc13f)

### Averaging
- Q: What are each of arithmetic, harmonic, and geometric means used for?
  
![image](https://github.com/user-attachments/assets/372faad6-f2ed-4b54-be26-6f4372647e7a)

### SPECmark
![image](https://github.com/user-attachments/assets/5a51f386-6249-4f30-ae83-c5dbefdef0b9)

## 1.4 Iron Law of CPU Performance
- Q: What is the iron law? latency = ?
- Q: What does instructions/program depend on?
- Q: What does cycles/instruction depend on?
- Q: What does seconds/cycle depend on?
![image](https://github.com/user-attachments/assets/dab1415f-6b8b-4cdd-b953-505fb38cc64a)

### Danger: Partial Performance Metrics
![image](https://github.com/user-attachments/assets/8127ed66-272b-453b-8496-295afbeee5ee)

### MIPS and MFLOPS (MegaFLOPS)
![image](https://github.com/user-attachments/assets/0345c241-ef8e-4ff2-a373-301196bf6ab3)

## 1.5 Applying the Iron law (with examples)
### Danger: Partial Performance Metrics 2
![image](https://github.com/user-attachments/assets/461d13ac-2c12-480a-8382-900b03648ff5)

### Cycles per Instructions (CPI)
![image](https://github.com/user-attachments/assets/c11037cb-be6d-4bac-a155-4684e499f305)

### A CPI Example
![image](https://github.com/user-attachments/assets/79257df1-ab4d-4fb0-a1ae-94f659da1627)

### Another CPI Example
![image](https://github.com/user-attachments/assets/a7233b1e-2c55-4e27-ba2e-2b66d0d30267)

### Increasing Clock Frequency: Pipelining
![image](https://github.com/user-attachments/assets/fa525956-dc0e-471f-b954-bd20be8f2c83)

![image](https://github.com/user-attachments/assets/bd871a3f-e6c4-46c0-851f-b54be71458b4)

### CPI and Clock Freqeuncy
![image](https://github.com/user-attachments/assets/5938457c-bb2d-430b-86cf-d0bea991c40f)

### Measuring CPI
![image](https://github.com/user-attachments/assets/b592a488-44ca-40f9-8246-8b6372ac9eee)

## 1.6 Amdahl's Law and Little's Law
### Amdahl's Law
- Q: What is Amdahl's law?
  
![image](https://github.com/user-attachments/assets/97b59dfd-dadb-4df9-b8b8-b476ce0c0762)

### Amdahl's Law Example
![image](https://github.com/user-attachments/assets/d98e06fa-2f53-4691-8007-70699c51939b)

![image](https://github.com/user-attachments/assets/a6880ac0-8b42-4270-ab05-1dfc5970b9e5)

![image](https://github.com/user-attachments/assets/33a8a865-72a0-40bb-b60c-ae69a253c40c)

- Q: If you can parallelize 90% of your program, what is the highest speedup you can achieve?
  
![image](https://github.com/user-attachments/assets/286ef893-623e-401e-b9bb-efb189e7eaf0)

### Little's Law
- Q: How big a wine cellar do you need if your family buys 1 bottle a week, drink 1 bottle a week, and the wine drank needs to be aged for 5 years?
- Q: What is Little's law?
  
![image](https://github.com/user-attachments/assets/b2d5ffdc-27e5-480c-9b63-dbe9bc1dd1ab)

![image](https://github.com/user-attachments/assets/8cb65b5a-a1d2-44ba-a960-39ec414dedfb)

# Knowledge check
- Q1: If machine A takes 30 seconds to execute a program and machine B takes 60 seconds, then machine A is 100% faster than machine B.
- Q2: The MIPS (Millions of instructions per second) metric accurately captures the performance of a computer.
- Q3: The maximum speedup acheivable by optimizing 20% of the execution time is 25%
- Q4: If each disk access takes 5 ms on average, and each access fetches a 4KB data block, how many concurrent accesses must a disk support to achieve a throughput of 400 MB/s.
- Q5: Deeper pipelines increases the CPI. (Ignore all pipeline hazards).
- A1: True
- A2: False
- A3: True
- A4: 500
- A5: False
