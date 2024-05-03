# Large Multiprocessors (Directory Protocols)

## Credit Based Flow Control

### Flow Control
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/04ebd19f-6c0d-4e64-91c6-49479b5ebc8f)

### On/Off with Combinational Stall Signal
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/32ee1412-4504-4b10-9edc-d0ccae7d2ba6)

### On/Off with Pipelined Stall Signal
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f06b3fdf-06e6-4563-b776-0c338b97416a)

### On/Off with Partial Pipelined Stall Signal
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c27c6325-28ee-4c8d-aba0-2253bf3b11b4)

### Credit-Based Flow Control
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c7775a67-c2c1-4949-b765-3d51347464fa)

## Deadlock

### Deadlock
- Q: Explain deadlock in this example.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/9c6d5322-e30a-413c-96a1-6ae1c5b07f2a)

- A: Node 1 claims link 12. Node 2 claims link 23. Node 3 claims link 31. Now Node 1 needs link 23 to send to 3, but it is already
- acquired by another node. Same for other nodes.

### Deadlock Example (Waits-for and Holds analysis)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/82f05e89-75bc-43dc-a261-34ddab3a7d25)

### Deadlock Avoidance vs Deadlock Recovery
- Q: Why might we not want deadlock avoidance?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3395ff8d-5a40-4951-9b19-3e01218b426b)

- A: It is very expensive.

## False Sharing

### Performance of Symmetric Shared-Memory Multiprocessors
- Q: What are the 4 Cs of cache misses?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/40f85a9a-47e8-4291-a59a-16bd63c68ee0)

### Coherency Misses
- Q: Explain what true sharing misses and false sharing misses are.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/b92ab176-0a86-46ee-a732-424739197750)

- A: True sharing miss - a word produced by a processor in a block is used by another processor. False sharing miss - words accessed by different processors happen to be in the same block.

### Example: True v. False Sharing v. Hit?
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ca5318aa-5558-4bf4-ba72-088c63d8d5e4)

### MP Performance 4 Processor Commercial Workload
- Q: Why do true and false sharing misses stay the same?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f0315138-3be4-4db9-8430-cbc7e31e727e)

- A: Because block size stays the same.

### MP Performance 2MB Cache Commercial Workload
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/68099fc6-d26e-4bf2-a1cb-54aeff9d4879)

## Introduction to Directory Coherence

### Directory Coherence Motivation
- Q: What is a downside of snoopy protocols?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0441548e-9fea-49b9-822d-2c6d43c20147)

### Directory Cache Coherence
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/47098954-1a2a-4fd7-a462-2f97b1c8bb96)

### Distributed Shared Memory
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0128e78e-32be-4f11-a917-dcec0c457af7)

### Non-Uniform Memory Access (NUMA)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a72dadbc-463d-4752-a853-42650df343f9)

cc - cache coherence

### Multicore Chips in a Multi-chip System
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/02167084-d4e1-4617-a76d-d0dba8bc59bb)

## Implementation

### Address to Home Directory
- Q1: Why do we not want to use virtual addresses?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/06780167-00ab-4b51-80e5-aef700ff73d9)

- A1: Sharing data between many systems. We have gone through TLB.

### Basic Full-Map Directory
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/59133eb5-c6a4-4789-80ff-95db53e5244f)

### Cache State Transition Diagram
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/84563eb0-a0e1-445f-9d21-85e0f5e7b2dc)

### Cache State Transition Diagram
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a5b3833f-f033-4916-b5a1-89ca97cfd7b1)

### Directory State Transition Diagram
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/73547f60-67a0-44cf-a299-38b17497edd2)

Even if we used MESI for cache, we could still use USE for directory.

### Message Types
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/bf54889d-f66f-4bb4-8759-5bb949054ee7)

## Scalability of Directory Coherence

### Multiple Logical Communication Channels Needed
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/73368031-0355-41cb-bf9e-9eb163a63a29)

### Memory Ordering Point
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/72f97b07-05ab-4b75-ac5e-146c77189367)

### Scalability of Directory Sharere List Storage
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/836413ac-a559-4443-8846-975d29d0e02d)

### Beyond Simple Directory Coherence
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e83dd798-64c6-45f8-9d18-49f23f702062)
