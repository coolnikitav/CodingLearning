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
