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

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0208627f-0ec9-4cfd-9e0b-b33cd1ea3439)
