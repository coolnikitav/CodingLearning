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
