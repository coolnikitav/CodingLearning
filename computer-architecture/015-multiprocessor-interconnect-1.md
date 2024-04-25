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
