# VLSI 

IC  | | Num of transistors
--- | --- | ----
SSI | small-scale integration | 1 to 10
MSI | medium-scale integration | 10 to 500
LSI | large-scale integration | 500 to 20k
VLSI | very large-scale integration | 20k to 1m
ULSI? | ultra-large-scale integration | > 1m

## Advantages of CMOS
- Low power (low power dissipation)
- Fully restored logic levels (almost full 1 and full 0)
- On and Off times are similar
- High integration possible (can pack them closely and stack them)
- High performance

### Technology
Minimum feature size - channel length
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/5f685786-aa89-4ca9-9b48-f6369d4c21e2)

## Design Styles

### Full-custom 
Standard cell library + Custom design

Companies: TSMC

Advantages: very good performance, low power, low area, efficient.

### Semi-custom

Only uses standard cell library (Gates, FFs, Latches, Buffers, etc...)

### FPGA

2 main players: Xilinx and Altera (Intel)

Good for prototyping

### Gate array

PAL, PLA

Fab without routing.

Small level functions, low performance

----------------------------------------------------------

Full-custom and semi-custome are ASIC
