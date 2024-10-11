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

## Module 7.9 Replacement and Write-Handling

### Q3. Block Replacement
![image](https://github.com/user-attachments/assets/2f28d950-67e8-44be-8e44-8685fee9f00b)

### NRU
![image](https://github.com/user-attachments/assets/2bf9081e-3987-440c-96d3-0c9f755dd38f)

### Writes
![image](https://github.com/user-attachments/assets/1310dd46-c224-4e71-a2e9-16adfdee711a)

### Tag/Data Access
![image](https://github.com/user-attachments/assets/d29ae30d-cbd3-4a6d-80bc-cf2ffd757aa3)

![image](https://github.com/user-attachments/assets/505b1d9b-c7e5-45fb-9743-448282770cf9)

![image](https://github.com/user-attachments/assets/3faeba28-4cb0-43c7-9ee3-e3f77dc7a1a7)

### Write-Through vs Write-Back
![image](https://github.com/user-attachments/assets/86d72e38-03b9-4712-a35b-e554de74f980)

### Write-allocate vs Write-non-allocate
- Q: Which one is more common for write-through and which one for write-back?

![image](https://github.com/user-attachments/assets/a61e9e12-d0e6-4a37-97cd-fc3c897e15d4)

### Buffering Writes 1 of 3: Store Queues
![image](https://github.com/user-attachments/assets/adbc0592-21f4-48a5-8d93-899951156a94)

### Buffering Writes 2 of 3: Write Buffer
![image](https://github.com/user-attachments/assets/418239eb-4e57-461f-b6b5-b622d32de425)

### Buffering Writes 3 of 3: Writeback Buffer
![image](https://github.com/user-attachments/assets/c36a9281-a2a4-4595-82c7-2b84faf8549b)

## Module 7.10 Quantifying Cache Overheads

### Calculating Tag Overhead
![image](https://github.com/user-attachments/assets/b86bb03f-9da8-4c6d-b387-de7be2e31969)

### Cache Type
- Q1: What does dynamic response mean?

![image](https://github.com/user-attachments/assets/dbada6e1-bdf7-49e5-aec3-f2ff2e16b5ac)

- A1: If we have a small loop that accesses a lot of data, we can have a small portion of the unified cache be instructions and the rest be data.

### Cache Type
![image](https://github.com/user-attachments/assets/072c9406-7206-4e1c-8e9d-c4d7d722ff53)

Note: cycles-lost-to-interference because of structural hazards where memory and fetch are in the same cycle

## Module 7.11 The 3C Model

### Advanced Caches
![image](https://github.com/user-attachments/assets/b57d73d2-02af-450f-8189-c8dc16f8be1a)

### Classifying Misses: 3(4) C Model
- Q: What are the 4 Cs?

![image](https://github.com/user-attachments/assets/ac7f480c-d6bd-4a3d-80a6-cc90aba63ed2)

### Fundamental Cache Parameters
![image](https://github.com/user-attachments/assets/5f57466d-d629-4c12-9423-9ade952b8890)

### Increase Cache Size
![image](https://github.com/user-attachments/assets/ee745183-5625-4983-87ba-c6f46321c318)

### Block Size
![image](https://github.com/user-attachments/assets/c64bde0d-dd06-449f-b8e8-fddf2e37d644)

### Effect of Block Size on Miss Rate
![image](https://github.com/user-attachments/assets/cc56b009-88db-4768-98bd-b1c2569840cd)

### Block Size and Tag Overhead
![image](https://github.com/user-attachments/assets/cc26700b-7678-4b39-9539-96c3f31c0737)

### Increase Associativity
![image](https://github.com/user-attachments/assets/a3cb8ba4-243c-4d73-a1f1-032bb4d51d4a)

### Mark Hill's "Bigger and Dumber is Better"
![image](https://github.com/user-attachments/assets/0fed678d-eef5-4943-87b7-56cd68b3c0d0)

![image](https://github.com/user-attachments/assets/0525bab7-7a39-47c1-982e-92b392c30b13)

## Module 7.12 Advanced Techniques: Software Restructuring

### Advanced Caches
![image](https://github.com/user-attachments/assets/d575bfbc-a653-4d4c-9a2c-082cd7536aaf)

### Software Restructuring: Data
![image](https://github.com/user-attachments/assets/bc8523c4-c5fb-4e8f-880a-c484ab842847)

### Restructuring Loops
- Q: What is loop fusion and loop fission and why would you use them?

![image](https://github.com/user-attachments/assets/d7f1a4ea-229d-427d-ab56-b04de60fa5eb)

### Array Merging
![image](https://github.com/user-attachments/assets/22716e22-cf1b-40d6-a0ae-dc353dc0222c)

### Software Restructuring: Data
- Q: What is loop tiling/blocking?
  
![image](https://github.com/user-attachments/assets/620dca37-19fb-41d9-923b-6aa161f5d3db)

### Blocking/tiling
![image](https://github.com/user-attachments/assets/3864871a-590f-46b4-99b1-bfc024a865d0)

### Software Restructuring: Code
![image](https://github.com/user-attachments/assets/417eed9f-dafd-44c2-a8fa-d5e066172aaf)

## Module 7.3 Advanced Techniques: Prefetching

### Nature of Capacity Misses
![image](https://github.com/user-attachments/assets/306355dc-83c4-42cf-aca1-c607136dfeb3)

### Reducing Capacity Misses: Prefetching
![image](https://github.com/user-attachments/assets/983968ad-ded9-4827-beea-88c8db1088b8)

### Software Prefetching
![image](https://github.com/user-attachments/assets/16710e6c-b88e-4b36-a924-9bceb183fe3e)

### Hardware Prefetching
![image](https://github.com/user-attachments/assets/e77f5e9a-3ddc-4878-a877-9c9c81c378fb)

### Address Prediction for Prefetching
![image](https://github.com/user-attachments/assets/cf157548-afec-4ac9-b098-782207a11d78)
