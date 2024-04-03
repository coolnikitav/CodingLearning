# Memory Protection
## Memory Management Introduction
### Memory Management
- From early absolute addressing schemes, to modern virtual memory systems with support for virtual
  machine monitors
- Can separate into orthogonal functions:
  - Translation (mapping of virtual address to physical address)
  - Protection (permission to access word in memory)
  - Virtual Memory (transaparent extension of memory space using slower disk storage)
- But most modern systems provide support for all the above functions with a single page-based system

### Absolute Addresses
EDSAC, early 50's
- Only one program ran at a time, with unrestricted access to the entire machine (RAM + I/O devices)
- Addresses in a program depended upon where the program was to be loaded in memory
- But it was more convenient for programmers to write location-independent subroutines:
  use the subroutine in different portion of your program

How could location independence be achieved?
- Linker and/or loader modify addresses of subroutines and callers when building a program memory image

- Static linker takes multiple compilation units (compiled source files...) and put them all into one program,
resolving all addresses in that program. Dynamic linker resolves the addresses at runtime.
- Loader takes binary off a disk and puts it into memory

### Bare Machine
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f5fbb5bf-1303-468c-8478-9f2a28b6e2c3)
- In a bare machine, the only kind of address is a physical address
- We will call addresses that touch main memory, physical addresses
- Virtual address is an address that the processor uses that might be translated somehow to a physical address in main memory

## Base and Bound Registers
### Dynamic Address Translation
Motivation
- In the early machines, I/O operations were slow and each word transferred involved the CPU
- Higher throughput if CPU and I/O of 2 or more programs were overlapped
  - How? => multiprogramming with DMA I/O devices, interrupts

Location-independent programs
- Programming and storage management ease
  - => need for a base register (all addresses from prog 1 have a certain offset and all addresses from prog 2 have a certain offset, all addresses from OS have 0 added)
 
Protection
- Independent programs should not affect each other inadvertently
  - => need for a bound register (program can only access a certain range of addresses)
 
Multiprogramming (running 2 programs at the same time) drives requirement for resident supervisor software to manage context switches between multiple programs

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/73c7a8dd-9569-46b6-8c87-8136c3e32c29)

### Simple Base and Bound Translation
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/23b9423e-4b91-40cf-8abf-8ba4b3cfba01)

If effective address is greater than the bound, you get a violation

### Separate Areas for Program and Data
Each program has one base and one bound register. It is possible to have two programs share data. Often times programs will share the program code but not data.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/9c9e4e5f-112d-4ff4-90be-54fc7ca5b3d0)

### Base and Bound Machine
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/de402581-2129-44ca-b998-a4a25b28084c)

### Memory Fragmentation
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d0207bdf-97a2-443b-a2cb-07a2efbe0886)

## Page Based Memory Systems
### Page Memory Systems
- Processor-generated address can be interpreted as a pair <page number, offset>
- A page table contains the physical address of the base of each page:
  ![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7c58ffaf-45cb-4fe9-a9eb-18ce935a55c8)

### Private Address Space per User
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/4d52d9e7-f235-4a7a-b211-264f08741384)

OS can go touch memory without going through a mapping layer

### Where Should Page Tables Reside?
- Space required by the page tables (PT) is proportional to the address space, number of users,
  (inverse to) size of each page, ...
  - Space requirement is large
  - Too expensive to keep in registers
- Idea: keep PTs in the main memory
  - Needs one reference to retrieve the page base address and another to access the data word
    - doubles the number of memory references!
  - Storage space to store PT grows with size of memory
 
### Page Tables in Physical Memory
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d5628184-2667-4280-945d-02a826f20aeb)

Note: the page tables themselves still need to be contiguous, which could lead to fragmentation

### Linear Page Table
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/60eb0e35-b772-45f3-a134-0e35546019d1)

### Size of Linear Page Table
- With 32-bit addresses, 4-KB pages and 4B PTEs:
  - 2^20 PTEs, i.e, 4 MB page table per user per procedd
  - 4 GB of swap needed to back up full virtual address space
- Larger pages?
  - Internal fragmentation (Not all memory in page is used)
  - Larger page fault penalty (more time to read from disk)
- What about 64-bit virtual address space???
  - Even 1 MB pages would require 2^44 8B PTEs (35TB!)
- What is the "saving grace"?
  - Go to a different arrangement of page tables. Some locations of page tables don't get used

### Hierarchical Page Table
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/abcf38d4-21c6-4029-abf8-0853ee2957f2)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/fb40f400-0a38-4f95-8d55-f699de353ef7)
