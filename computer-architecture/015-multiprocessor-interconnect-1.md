# Multiprocessor Interconnect 1

## More Cache Coherence Protocols

### MOESI (Used in AMD Opteron)
- Q: What are all the states in MOESI?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/824134d8-e36f-45f8-9e33-52b94e3a7b34)

### MESIF (Used by Intel Core i7)
- Q: What are all the stateis in MESIF?

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/02a6b153-880b-46d9-afcb-1a55d014437d)

### Scalability Limitations of Snooping
- Caches
  - Bandwidth into caches
  - Tags need to be dual ported or steal cycles for snoops
  - Need to invalidate all the way to L! cache
- Bus
  - Bandwidth
  - Occupancy (As number of cores grows, atomically utilizing bus becomes a challenge)
 
### False Sharing
- Q: What is false sharing?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/15ffaf68-8b4f-4661-870b-f76ebfe69aaa)

## Introduction to Interconnection Networks

### Overview of Interconnection Networks: Buses
- Q: What are some of the issues with the busses?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/fe7d0528-f951-4aad-8bc4-ae5b5c2a0e31)

- A: Capacitance issues, wire delay, having to wait for all cores to communicate with all other cores every clock cycle (?)

### Overview of Interconnection Networks: Point-to-point/Switched
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d9c10359-2c18-4f09-a2ae-b725b9df6f00)

## Message Passing

### Explicit Message Passing (Programming)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/29ecfdbc-8434-40e0-b3d7-bc0301afb5a6)

### Message Passing Interface (MPI)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/3b4241d9-53c8-49ef-b38c-bdd84f3764e6)

### Message Passing vs Shared Memory
- Q: What are the differences between message passing and shared memory?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/cefae5a4-9a15-459c-924c-74775d7c46dc)

### Shared Memory Tunneled over Messaging
- Q: How does software and hardware tunnel shared memory over messaging?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d262f861-8ec0-4198-80fc-bc9fcec2eb5c)

### Messaging Tunneled over Shared Memory
- Q: How does software tunnel messaging over shared memory?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d00f6290-6140-48dd-9dee-1551c8d51143)

## Interconnect Design

### Interconnect Design
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/959f7b18-ea38-4370-b8b7-f82b85cba3b3)

### Anatomy of a Message
- Q: What is a flit? What is a phit?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7711ba35-e116-4f65-a9cc-071f05674c94)

SRC - source | DST - destination | LEN - length

### Switching
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d4921a2b-0748-4375-99f2-ac2f7cb4a4fb)

### Topology
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/89c410f3-13b6-4d4f-8151-51a66ab573dc)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0c01e0fa-dd95-4664-8e61-cd48c4459577)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0d960093-6066-4131-ad08-69dba9854067)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7754aac0-96b5-4632-abd9-6ffb4438fcda)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1c15b419-a5bc-4f71-b865-a80062ecb2bf)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/466f372f-58c8-4275-969f-e4aee19bbb7b)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c7f93ae4-c1d9-4ba4-822e-82da3862b452)
