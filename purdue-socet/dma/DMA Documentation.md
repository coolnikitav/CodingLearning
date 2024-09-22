# Contents
1. DMA Motivations 
2. DMA Features and Functionality 
3. DMA Registers and configuration 
4. Internal DMA module design 
5. Cache Coherence
6. DMA Triggers
7. Transaction Diagrams and example use cases:
    - Memory to Memory Flow
    - Memory to Peripheral flow without DMA triggers
    - Memory to Peripheral flow with DMA triggers
8. SoC-Level Integration

# DMA Motivations
The DMA controller is an integral part of a modern System on Chip (SoC). The three key components of any SoC or embedded system are the CPU, memory, and peripherals (and I/O). The CPU is responsible for moving data around between the different components. It does this by using two instructions: the load instruction and the store instruction. The load instruction loads data from a specified memory address or peripheral, and the store instruction stores data to a specified memory address or peripheral. The problem with solely relying on load and store instructions to move data around the SoC is that load and store instructions take many cycles to complete. Peripherals and memory are much slower than the CPU, and they take a long time to process and complete the loads and stores. Because of this, it is very common for a CPU to stall, which is when the CPU is sitting idle waiting for the memory and/or peripheral to process the load or store instruction. The CPU ultimately wastes a significant amount of both time and power that could have been used to perform other actions. In order to prevent the CPU from wasting time and power on load and store operations, a DMA controller can be utilized. In order to improve these operations, the addition of a DMA Controller in practice, would provide improvements in terms of effective cycles for data transfers across the SoC. The DMA controller on a basic level is a CPU that can only do loads and stores. Rather than forcing the CPU to wait for a memory or I/O operation to finish prior to executing further instructions, the DMA controller can fulfil these operations in parallel with the CPU. 

# DMA Features and Use Cases
- Memory to Peripheral Transfers
- Peripheral to Memory Transfers
- Memory to Memory Transfers
- Memory to Memory Transfers 
- Supports Peripherals that have built-in DMA support (with req and ack lines) (DMA Triggers)
- More info in transaction diagrams below
  
# DMA Registers and Configuration
The DMA has several internal registers that are used to configure the operation of the DMA. More specifically, there is a source address register, a destination address register, a transfer size register, a control register, and a status register. The CPU configures the source address, destination address, and transfer size by setting the corresponding values in the source address register, destination address register, and transfer size register respectively. The control register is to set other configurable operation parameters, such as the word size, the direction of the transfer (peripheral to memory or memory to peripheral, etc.), and more. The status register is used to display any errors that may occur during operation. To write to the registers, The CPU simply needs to write to their memory mapping. The specific registers and their bits are shown below:

### Source Address Register - Offset 0x4 – Read/Write
- Bits: 31-0
- Purpose: Source Address
- Description: The source address from which the memory should be transferred from
  
### Destination Address Register - Offset 0x8 – Read/Write
- Bits: 31-0
- Purpose: Destination Address
- Description: The destination address to which the memory should be transferred to

### Transfer Size Register - Offset 0xC – Read/Write
- Bits: 31-0
- Purpose: Number of bytes to be transferred
- Description: The number of bytes to transfer 

### Control Register - Offset 0x10 – Read/Write
- Description: DMA Control register
- Bit[0] : EN : should be set to start the transfer 
- Bit[1] : TCIE : is the Transfer Complete Interrupt Enable
- Bit[2] : HTIE : is the Half Transfer Interrupt Enable
- Bit[4] : SRC : Is the source a peripheral or memory (0: Source is Memory, 1: Source is Peripheral)
- Bit[5] : DST : Is the source a peripheral or memory (0: Source is Memory, 1: Source is Peripheral)
- Bit[6:7] : PSIZE : Peripheral Size (00: 8-bit, 01: 16-bit, 10: 32-bit)
- Bit[8] : TE : DMA Trigger Enable           
- Bit[10] : CIRC: Circular Mode   
- Bit[11]: IDST: Increment destination address every read/write
- Bit[12]: ISRC: Increment source address every read/write

### Status Register - Offset 0x14 – Read Only, cleared by Reading
- Bit[0] : Transfer complete, set by hardware, cleared by reading from software
- Bit[1] : Transfer Error, set by hardware, cleared by reading from software
  
# Internal DMA Module Design
### General Overview
The DMA Controller is made up of a few main components: The registers, the read control unit, the write control unit, a counter, an memory arbiter, and a median control unit. The registers are used to configure the operation of the DMA. More specifically, there is a source address register, a destination address register, a transfer size register, a control register, and a status register as described in the previous section. The read control unit reads data from the source address and places it in the FIFO. The write control unit takes data out of the FIFO and writes it to the destination address.

### Control Units

The most important components of the DMA are the read control unit and write control unit. The read control unit is implemented using a state machine. It works by reading a chunk of data from the source address and placing it into the FIFO along with the corresponding destination address. The write control removes data blocks from the FIFO, and sends them to the destination. The read and write control units act independent of each other. This means that there is a significant chance that both control units try to access memory simultaneously. Unfortunately, the current bus only supports a single transaction at at a time, so a memory arbiter is used to arbitrate between the control units in case they try to access the bus concurrently.  The DMA can also be directly accessed by peripherals that have direct DMA support via the DRQ and DACK lines on the DMA. A basic version of the read and write FSMs are shown below:

Read Control Unit on Left, Write control unit on right 



# Cache Coherence
Because the DMA is accessing the main memory directly, and the CPU has a cache, cache coherency becomes a significant issue. As mentioned in the background section, the CPU wastes a lot of time when it accesses main memory. Although this task can often be offloaded to the DMA, there are times when the CPU needs to load the data itself. This happens when the CPU needs to manipulate the data in memory. An example of this would happen is if every element of an array needed to be multiplied by 2. In order to mitigate some of these memory access times, the CPU has a cache, or a small fast piece of memory that stores recently used pieces of data. If the DMA bypasses the cache and writes to main memory, it can cause the data in the cache to become outdated, which will cause the program to execute incorrectly. To avoid this problem, using the DMA requires the use of memory attributes such that the DMA only uses non-cacheable regions of data. At the time of writing, the memory attribute implementation is in progress. 

# DMA Triggers
Our DMA design supports the use of DMA triggers, or direct-DMA-interrupts. Without DMA triggers, the CPU needs to manually enable the DMA every time it needs to be used (shown in a transaction diagram below). Whenever a peripheral needs data, the peripheral interrupts the CPU, and the CPU then enables the DMA from the interrupt service routine. In this case, the CPU is basically being used as a middleman/mail carrier, as the peripheral interrupts the CPU then the CPU enables the DMA. DMA triggers solve this problem by allowing peripherals to directly interrupt the DMA when low on data. To utilize DMA triggers, the peripheral device must have a request (DRQ) line and an acknowledgement (ACK) line connecting the peripheral to the DMA controller. The flow is described below

1. The DMA must be configured to use DMA triggers via its configuration register
2. The peripheral must be configured to use DMA triggers via its configuration register
3. When the peripheral needs data, it pushes the DRQ line high to "trigger" a DMA transfer
4. The DMA transfers data in accordance to the value set in the DMA's transfer size register to the peripheral 
5. The DMA pushes the ACK line high for a cycle indicating to the peripheral that the transfer is complete 
6. The peripheral de-asserts the DRQ line after receiving the acknowledgement 

After completing the DMA, we modified the existing SPI peripheral to support DMA transfers the SPI can be configured to create a DMA trigger when its TX buffer/RX buffer is below/above some preset watermark. See the SPI peripheral as a guide to implementing DMA trigger support on future peripherals.  

# Transaction Diagrams and Example Use Cases With Waveforms
The DMA controller can be used for the following purposes:
- Memory to Peripheral Transfers
- Peripheral to Memory Transfers
- Memory to Memory Transfers
- Memory to Memory Transfers 
- Supports Peripherals that have built-in DMA support/DMA trigger support
- Supports Peripherals that do not have built-in DMA support/DMA trigger support (using CPU interrupts)

Below are some transaction diagrams that show the sequence of events for three different use cases:
- Memory to Memory Transfer: This is the most basic form of DMA transfer
- Peripheral to Memory Transfer (no DMA support built-in to peripheral): The CPU uses interrupts to facilitate transfers between the DMA and peripheral 
- Peripheral to Memory Transfer (with DMA support): The CPU is used for configuration initially then it is no longer required for the rest of the transaction

# Memory to Memory Flow
- This is the most basic form of DMA transfer
- This form of DMA transfer involves transferring data from one memory location to another memory location
- After setting the registers, the DMA controller transfers data from source to destination in the specified word size
- Below the sequence diagram, there is a step-by-step flow of the sequence diagrams with the corresponding waveforms

### Step 0: Software Program/Preload data into RAM
- This image shows a basic program that can be used to do a simple memory-to-memory transaction using the previously described sequence diagram
- To start, the RAM at the source address of 0x8100 is preloaded with data as described in software
- The data in RAM is visible in the waveform above 

### Step 1: Set Registers of DMA Controller
- The source, destination, transfer size, and configuration registers are all set via the software program from step 0
- The register data is successfully updated in the DMA controller as shown in the waveforms 
  - Start address of 0x8100
  - Destination address of 0x8200
  - Transfer size of 5 words with 4 bytes per word
  - The source and destination address will be incremented by one after a word is transferred 
  - Interrupt enabled 

### Step 2: Transfer Data
- This step involves transferring data from the source address to the destination address 
- The program called for 5 words from source to destination, where each word was 4 bytes
- The state[3:0] describes the state of the read control unit
    - The read control unit goes into the READ state 5 times - once for each word
- The state[2:0] describes the state of the write control unit
    - The write control unit goes into the WRITE state 5 times - once for each word
- After completing the transaction, the read control unit goes to the finished state as expected 

### Step 3: Transfer Complete Interrupt
- The final step involves interrupting the CPU to signal that the DMA transfer is complete
- This waveform is a zoomed-out/continuation of the previous waveform from step 2
- As the read control unit goes into the finished state, the status register gets updated to 1 to indicate the transfer is complete as shown in the waveform
- The DMA interrupt is also triggered to signal that the transfer is complete 
- After the status register is read, the read control unit returns to the IDLE state and the interrupt is cleared as marked by No.3 on the waveform

# Memory to Peripheral Flow (No Triggers)
- The next transaction diagram is for a memory to memory flow
- The peripheral is configured to raise an interrupt when its input data buffer/FIFO is low on data
- When this interrupt is raised, the CPU enables the DMA to initiate a transfer 
- This process is repeated indefinitely 

# Memory to Memory Flow with DMA Triggers

### Step 1: Set Registers of Peripheral in Question
- In this example, the peripheral being used is the SPI peripheral 
- We modified the existing SPI peripheral to support DMA triggers 
- As shown in the waveform, the dma_tx_trigger enable bit is set
  - This enables a DMA trigger when the SPI TX buffer is running low on data
  - The watermark is set to 0x5 
  - This means if there are 5 or less bytes in the TX buffer, a DMA transfer will be triggered 

### Step 2: Configure DMA registers
- Similar to the memory-to-memory transaction walkthrough earlier in the documentation, the DMA registers are set 
- This time, the control register is set for DMA triggers
- 3 word transfer size
- word size of 4 bytes
- source address of 0x8100
- destination address of 0x8003000C, which is the address of the SPI TX buffer 
- DMA triggers enabled
  
### Step 3: Peripheral Data Request
- As described in the previous step, the SPI watermark is set to 0x5
- The SPI TX-buffer is currently empty
- Since the amount of data in the buffer is lower than the watermark (0 < 5), the DMA gets triggered via the DRQ (DMA request) line as shown in the waveform 

### Step 4: Data Transfer and ACK
- DMA request sent from SPI
- DMA transfers 3 bytes
- DMA sends ACK after all 3 bytes are transferred as shown in waveform, but amount of data still less than watermark (3 < 5)
- Second DMA request sent from SPI
- DMA transfers 3 bytes
- DMA sends ACK after all 3 bytes are transferred as shown in waveform
- Amount of data in SPI TX-buffer now exceeds watermark (6 > 5)

# SoC Level Integration
As shown on the image below, the DMA integration is between several of the components on the AFTx06 chip. The DMA control acts as both a master and slave on the AHB-lite interface. It acts as a slave to receive configuration data from the CPU so it knows what types of transfers to complete. It acts as a master to initiate transfers to and from memory and peripherals. Therefore, it needs to be connected to both the AHB-lite slave initiator in the top level module, and it also needs to be an input into the AHB-lite master selection mux as shown in the diagram below. Additionally, because the DMA controller generates interrupts to the CPU, it needs to connect to the PLIC. Finally, it also needs to connect to each peripheral that supports DMA access for direct I/O triggers that bypass the CPU. 

Our current implementation of the AFTx06 system is implements all of the connections listed above. It supports DMA triggers with the existing SPI peripheral, PLIC interrupts, AHB-master, and AHB-slave transactions. 
