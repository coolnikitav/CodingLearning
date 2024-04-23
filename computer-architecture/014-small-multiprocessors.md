# Small Multiprocessors

## Bus Implementation

### Symmetric Multiprocessors
- Q: What is meant by symmetric in this context?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/eed4ba30-8cd2-416d-9510-3c532182c4d5)

### Multidrop Memory Bus
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0ca43fe9-e242-4a7d-be61-456f8fbe50de)

### Pipelined Memory Bus
- Q: What is the advantage of the pipelined bus?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0ca43fe9-e242-4a7d-be61-456f8fbe50de)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/21a286d9-8b89-4748-a37b-ee9e94f5e8ca)

- A: Instead of getting the control of the whole bus, access is pipelined and use only when needed.

## Cache Coherence

### Memory Coherence in SMPs
- Q: What happens in CPU-1 updates A to 200 in case of write-back and write-through.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e4d7f00d-70f9-4fe6-9a25-39599f27223e)

Stale values matter because the other CPU will not see the new value. There is no communication.

### Write-back Caches & SC
This is write-back cache:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/071db50b-b3e1-47a4-a732-5117d1157958)

Even SC consistent code can end up with inconsistent values when we introduce caches.

### Write-through Caches & SC
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/68ba87b5-fc8d-42c3-93b6-7354d7d29f56)

### Cache Coherence vs Memory Consistency
- Q: Explain cache coherence and memory consistency.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0f16b165-19cf-49f5-b68f-95e5e8ad526f)

## Bus-Based Multiprocessors

### Warmup: Parellel I/O
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/931e1baf-f09d-443d-b87b-860bcd1c3792)

### Problems with Parallel I/O
- Q1: How to have disk see the data thats in the cache?
- Q2: What could be some problem transferring data memory->disk and disk->memory?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/54b61596-a239-4e6e-800d-387747465ebb)

- A1: One option is to invalidate the cache and pull in the latest copy of the data.

## Cache Coherence Protocols

### Snoopy Cache
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d74b6177-442c-45c6-89ce-f865ebf63430)

- Q: What is meant by "do the right thing"?
- A: If a cache sees a memory transaction go by that it has an address for, it needs to take action.

### Shared Memory Multiprocessor
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/de7e7507-1e6d-45fe-982e-3aebcf761979)

### Update(Broadcast) vs. Invalidate Snoopy Cache Coherence Protocols
- Q: Explain write update and write invalidate protocols.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1638323f-6990-4b99-a5a4-7cddd03b16b4)

### Write Update (Broadcast) Protocols
- Q1: What is a write miss?
- Q2: What is a read miss?
- Q3: What happens during a write miss in this protocol? What happens during a read miss?

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/358b6e48-56f5-4df7-98a5-56deb1c8b6d1)

- A1: A write miss in cache happens when a processor attempt to write to an address in cache where data has been modified since it was fetched last time.
- A2: A read miss occurs when a processor tries to read data from an address in cache, but the data isn't there.
- A3: Read miss: main memory is always up to date, so you go there on a read miss.

### Write Invalidate Protocols
- Q: What happens during a write miss and a read miss.
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/5cee5586-d6c3-4c7e-abb8-cecd2959feb3)

### Cache State Transition Diagram: MSI Protocol
- Q: Explain the 3 states.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2519a632-6ac4-41a5-a2ec-1bd9e34b5d18)

- A: Invalid - you cannot read it. If you try reading data in your cache with an invalid tag, you will get a read miss. Modified - data in the cache has been modified relative to its value in the memory. Shared - you have a read-only copy of the data and someone else may have a read-only copy of the data.

### Two Processor Example (Reading and writing the same cache line)
- Q: Explain the example.
  
When computer system is reset, all cache lines are invalid

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ca09bcdf-889c-476b-ba01-28c247acdb01)

- P1 read miss
- P1 intent to write, then P1 reads or writes
- P2 read miss and P1 write back and transition to S
- P2 intent to write, then P2 reads or writes
- P1 reads, P2 writes back
- P1 intent to write, then P1 reads or writes
- P2 intent to write, then P2 write miss, P2 reads or writes
- P1 intent to write, then P1 write miss, P1 reads or writes

### Observation
- Q: What is a big rule of this system? (Revolving around M state)
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/11027090-4860-46a0-b503-829fd4326829)

### MESI: An Enhanced MSI Protocol
- Q: What is an advantage of the MESI protocol?

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0ea1927d-4bb1-400f-b721-da0377ce9365)

- A: If data is in E state, the processor has the exclusive read-only copy. Thus, if it wants to write, it doesn't have to communicate to everyone on the bus. This saves bandwidth.
