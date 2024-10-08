# Chapter 7

## Module 7.1 Memory Subsystem Basics

### Problem
- Q: Base CPI is 1.2. Every 5th instr is ld, memory access is 10 cycles. What is the new CPI?

![image](https://github.com/user-attachments/assets/04b20f47-9982-49f9-adb1-77fe1dbc4241)

### Motivation
![image](https://github.com/user-attachments/assets/199efcfc-09d5-4ac1-b11a-152e00a11082)

### Types of Memory
![image](https://github.com/user-attachments/assets/f98bf573-1d25-406b-a4e6-cf5d61fe88c1)

### Storage Technology Trends
![image](https://github.com/user-attachments/assets/46d621fc-fdf6-4717-bbac-a02cedf15c5c)

### The "Memory Wall"
![image](https://github.com/user-attachments/assets/855e3aeb-f874-41fb-9405-83bbd43d23db)

### Basic Memory Array Structure
![image](https://github.com/user-attachments/assets/f987983b-b434-47e8-865a-411f6414d24c)

### Physical Cache/Memory Layout
![image](https://github.com/user-attachments/assets/a4d3964d-2b58-4e09-ae24-cf2028124043)

![image](https://github.com/user-attachments/assets/e2d6c8c3-d3ca-468a-a3d9-025307b7e5c8)

### Challenge: CPU-Memory Gap
![image](https://github.com/user-attachments/assets/dee8232f-001f-4c93-b5d8-338e5d2317c8)

## Module 7.2 Understanding Locality

### Locality
![image](https://github.com/user-attachments/assets/b00785f0-debb-4545-9518-fdcec49b9e80)

### Two Flavors of Locality
![image](https://github.com/user-attachments/assets/37467b57-b6fd-423d-ac9d-f7ae4e319141)

### Connect Locality and Caches
![image](https://github.com/user-attachments/assets/010b57cc-0253-4a4f-924a-541f991497f4)

### Illusion of Speed and Capacity
![image](https://github.com/user-attachments/assets/c305189f-8df0-458e-96fc-af23d49fdaa4)

### Why Caches Work
![image](https://github.com/user-attachments/assets/76d831c9-ee36-4f62-8abd-dc843ea5a4e6)

## Module 7.3 Levels of the Memory Hierarchy: Key Differences and Similarities

### Exploiting Locality: Memory Hierarchy
![image](https://github.com/user-attachments/assets/36920a49-afda-4711-ac26-ae5e3f8db6cb)

### Concrete Memory Hierarchy
![image](https://github.com/user-attachments/assets/bc1ba1d1-7ed0-4b13-8031-8c1657938a36)

### Register <-> Main memory
![image](https://github.com/user-attachments/assets/aa0cd50f-f3ae-43dd-9071-25f15579ab85)

### Disk <-> Memory
![image](https://github.com/user-attachments/assets/2b89941e-9d76-4006-b62c-d9c64cb37745)

### Cache <-> Memory
![image](https://github.com/user-attachments/assets/012447a5-300c-4667-b2ed-6fc4114c9ddf)

### This Unit: Caches
![image](https://github.com/user-attachments/assets/75305b0a-46bb-42a2-8979-d8c0d54f9d98)

## Module 7.4 Basic Cache Operation

### Cache Operation
- Q: What is a frame in cache?

![image](https://github.com/user-attachments/assets/9060dbe7-8def-4177-af82-6abdb8b52e25)

Note: at startup, all valid bits are zero.

![image](https://github.com/user-attachments/assets/ef3ae2c2-c5f4-48f7-a773-ff7a34567b0c)

### Example of cache operation
![image](https://github.com/user-attachments/assets/7595ad49-e552-4a12-81fe-5e82ba80f129)

- Q: Fill in this cache:![image](https://github.com/user-attachments/assets/c2c08c58-439f-4dad-a73f-b830ebd110c8)

![image](https://github.com/user-attachments/assets/c6c24fd3-d9d0-4af0-9fe6-9c72411e19a4)

## Module 7.5 Multi-Word Cacheblocks

### 4KB, 4-byte Block Cache Operation
![image](https://github.com/user-attachments/assets/dedc4531-5d1d-4189-9125-d4b454166546)

### 16KB Size, 64-Byte Block
![image](https://github.com/user-attachments/assets/d0620fb8-bc0b-44a5-911d-ef45c829526b)

## Module 7.6 The Four-Question Framework

### 4 Questions for Memory Hierarchy
![image](https://github.com/user-attachments/assets/f68c2404-550d-4112-865b-b4e687bad2ed)

### Q1 Block Placement
![image](https://github.com/user-attachments/assets/9b37a3a0-ee74-4cab-b63b-4b2b51a15548)

### Block Placement
![image](https://github.com/user-attachments/assets/a79aede6-157b-44a3-9baf-57774d9d44bc)

### Block Identification Example: 1 KB Direct Mapped Cache with 32B Blocks
![image](https://github.com/user-attachments/assets/8243d4aa-1f2f-4c1c-a64c-357cbe299dd7)

### Another Extreme Example: Fully Associative
![image](https://github.com/user-attachments/assets/16e63d86-8c07-4969-a941-055bc22c2b8b)

### A Two-Way Set Associative Cache
![image](https://github.com/user-attachments/assets/4696a2a8-ac90-4854-abd0-7dfb758bd2b1)

### 4-way Set Associative Cache
-Q: Design a 4KB cache that is 4-way associative and has 4B blocks.

![image](https://github.com/user-attachments/assets/4ae32ad6-b6b3-4d59-a5a4-ce5ce293c5e6)

## Module 7.7 Designing a Cache From Its Parameters

### Associativity
![image](https://github.com/user-attachments/assets/97ddc6a2-a0dc-4665-8da4-676056ce9836)

### Set-Associativity
![image](https://github.com/user-attachments/assets/d78a5350-6a44-469e-a3ed-0d0be20cd81d)

### Terminology
![image](https://github.com/user-attachments/assets/80fe21cc-7042-419b-bbc7-bd5312b3d780)

### Organization Methodology
![image](https://github.com/user-attachments/assets/00ceefef-66d9-434c-826f-fa88d413e964)

### Cache Organization
![image](https://github.com/user-attachments/assets/f32fc503-e4a3-489f-b4f9-636fc13263b4)

## Module 7.8 Qualitative Benefits of Associativity

### Disadvantages of Set Associative Cache
- Q: What are some of the disadvantages?

![image](https://github.com/user-attachments/assets/1a7995bb-2af5-4474-96fe-1a94dd67cb1b)

### Associativity Spectrum
- Q: What is the relationship between missrate, complexity, and associativity?

![image](https://github.com/user-attachments/assets/ae49fdba-af74-4a64-aa10-ff0ef1c64df2)

### Performance
![image](https://github.com/user-attachments/assets/97130312-f04e-41de-a740-3d624c1104b0)
