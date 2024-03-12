# Bus Protocol: Verification of AXI Memory
AXI -  Advanced eXtensible Interface

AXI is a more general interface to a RAM
- Reads and writes can have variable latencies
- Write address and data can be sent at different times
- Reads and writes might not be issuable every cycle
- The user might not be ready to receive data every cycle
- Reads and writes can fail
- Reads and writes are issued in streams called bursts

5 groups of ports:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/df95adc5-54f1-4fab-9ee8-c5687b72308a)

### Read Bursts

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/cff1f714-638c-4289-8c07-c1747b560198)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/102c56aa-9f0b-41ff-be30-5da47755773f)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/905bd1ca-bb22-4d95-8c12-dde5c15a5c65)

arready is set to 1 when memory is ready to receive a new burst

user sets arvalid to 1 when they are ready to issue a new burst

when arready and arvalid are 1, transaction is acknowledged and it starts

when receiver of the data is ready, it will set rready to 1

when memory chunk is ready to be sent out, the memory will set rvalid to 1

when rready and rvalid are 1, the handshake takes place

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f1e55af6-0fc2-4320-a541-3b72a92c8f21)

arburst indicates the type of burst

araddr is the start address of the burst

arlen is the num of transfers in the burst minus one

arsize indicates how many bytes are in each transfer

rdata contains the actual data requested

rresp indicates whether the read actually succeeded

rlast is a flag that indicates whether the current piece of data coming out is last in a given burst

### Example
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/80f250d1-6597-4db7-a9dd-d3f7290598eb)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1324fba5-97cd-4883-a53f-7ec7dd757c72)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f11eb0e4-7a1e-4176-a84a-618ad2112d2c)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/57d10b75-f1b3-49e9-9946-00d8da567559)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c8aada23-b3cd-4395-9927-5907035f5c86)

### Write Bursts

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a8bb312e-033c-4789-930a-8863f4b97d65)

write_strb determines which bytes of the data you want to set

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ff18863d-5d5f-447f-8430-85f2757557b2)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/50f3617a-221e-4dee-9e32-8e6a3b7f7c2a)

awlen - number of transfers in the burst

wstrb has 1 bit for each byte in the wdata

### Example
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/44d445f4-aeaf-4969-b718-a425c1cf3991)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/da596a31-f2cb-4bd7-b039-106cec9af111)

### AXI

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0208627f-0ec9-4cfd-9e0b-b33cd1ea3439)
