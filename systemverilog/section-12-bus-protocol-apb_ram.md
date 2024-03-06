# Bus Protocol: Verification of APB_RAM

Advanced Peripheral Bus Signals
- Used to communicate with peripheral components
- Single chanel

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d613b276-df7d-4fe0-81a6-d80b089cd427)

Signals
- PCLK
- PRESETn - synch. reset
- PADDR - [31:0]
- PDATA - 8, 16, 32 bits
- PWRITE - 0 = READ, 1 = WRITE
- PSTRB - [3:0] - select which of the data bits are valid. 0 = [7:0], 1 = [15:8], 2 = [23:16], 3 = [31:24]
- PSEL - select slave
- PENABLE - enable
- PRDATA - [31:0] read data from slave
- PREADY - slave indicates when data is valid
- PSLVERR - slave error
- PPROT - [2:0], protection signal, 0 = priveleged/nonpriveleged, 1 = secure/nonsecure, 2 = data/control

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/71ad7e20-ba9b-4895-a1a2-396cfc6ba6f6)
