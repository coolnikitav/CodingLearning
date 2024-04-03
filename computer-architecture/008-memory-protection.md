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

## Translation and Protection
### Address Translation & Protection
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/dc849318-fa57-41db-9c6a-5df47bdedf55)
- Every instruction and data access needs address translation and protection checks

A good Virtual Memory (VM) design needs to be fast (~one cycle) and space efficient

### Translation Lookaside Buffers (TLB)
- Problem: Address translation is very expensive!
  - In a two-level page table, each reference becomes several memory accesses
 
- Solution: Cache translations in TLB
  - TLB hit -> Single-Cycle Translation
  - TLB miss -> Page-Table Walk to refill

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c01fad18-5736-494e-8d18-332ac7dacd01)

Valid, Read, Write, Dirty

Dirty bit shows whether the page has been accessed

### TLB Designs
- Q: Why is it likely that two entries conflict?
  
- Typically 16-128 entries, usually fully associative
  - Each entry maps a large page, hence less spatial locality across pages -> more likely that two entries conflict
  - Sometimes larger TLBs (256-512) entries are 4-8 way set-associative
  - Larger systems sometimes have multi-level (L1 and L2) TLBs
- Random (Clock Algorithm) or FIFO replacement policy
- No process information in TLB
  - Flush TLB on Process Context Switch
- TLB Reach: Size of largest virtual address space that can be simultaneously mapped by TLB
  - Example: 64 TLB entries, 4KB pages, one page per entry. TLB reach = 256 KB
 
### TLB Extensions
- Q: Why would we use the ASID and G TLB Extensions?
  
When you change between processes, you would change the base pointer. TLB is the cache of the page table. So when you change the base pointer, you would have to invalidate the entire TLB.

- Address Space Identifies (ASID)
  - Allow TLB Entries from multiple processes to be in TLB at same time. ID of address space (Process) is matched on.
  - Global Bit (G) can match on all ASIDs
- Variable Page Size (PS)
  - Can increase reach on a per page basis
 
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1e3f86d3-4618-45d0-abad-e0bd38c6570c)

## TLB Processing
### Handling a TLB Miss
- Q: How does hardware handle a TLB Miss?
  
- Software (MIPS, Alpha)
  - TLB miss causes an exception and the operating systme walks the page tables and reloads TLB. A priveleged "untranslated" addressing mode used for walk
- Hardware (SPARC v8, x86, PowerPC)
  - A memory management unit (MMU) walks the page tables and reloads the TLB
  - If a missing (data or PT) page is encountered during the TLB reloading, MMU gives up and signals a Page-Fault exception for the original instruction
 
### Hierarchical Page Table Walk: SPARC v8
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/8e249dd3-ec7a-4d78-9101-c67a257ce0b4)

### Page-Based Virtual-Memory Machine (Hardware Page-Table Walk)
- Q: What happens when there is a TLB miss?
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/19668d19-f74e-4f8b-b8cf-78a129836e3a)

If there is a miss, the walker stalls the whole processor and uses the base register to walk around in main memory and figure everything out.

### Address Translation: putting it all together
- Q: Describe what happens during TLB lookup hit and miss.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d356160a-41cd-4415-bd94-829d8840d38f)

### Modern Virtual Memory Systems (Illusion of a large, private, uniform store)
- Q: Explain demand paging. How could it cause the system to run out of memory?
  
- Protection & Privacy
  - several users, each with their private address space and one or more shared address spaces. page tables = name space
- Demand Paging
  - Provides the ability to run programs larger than the primary memory. Loads the furst page of the program. Then when second page is looked at, there is a page fault, so goes and loads it and continues executing.
  - Hides differences in machine configurations
 
The price is address translation on each memory reference

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/38015c74-9101-4dd3-a06f-e010fc75f36a)
