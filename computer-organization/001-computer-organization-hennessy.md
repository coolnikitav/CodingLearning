1.6 A given application written in Java runs 15 seconds on a desktop processor. A new
Java compiler is released that requires only 0.6 as many instructions as the old
compiler. Unfortunately, it increases the CPI by 1.1. How fast can we expect the
application to run using this new compiler? Pick the right answer from the three
choices below:
- Time/program = instr/program * clock cycles/instr * sec/clock cycle
- New time/program = old time * 0.6 * 1.1 = old time * 0.66 = 15*0.66 = 9.9sec



1.6
![image](https://github.com/user-attachments/assets/bfc3dcc6-e107-4f2b-9b6a-4ad5302738e5)
- Sequence 2 executes the most instructions (6)
- Clock cycles 1 = 2 * 1 + 1 * 2 + 2 * 3 = 10
- Clock cycles 2 = 4 * 1 + 1 * 2 + 1 * 3 = 9
- Sequence 2 will be faster
- CPI1 = 10/5 = 2
- CPI2 = 9/6 = 1.5



1.6 Suppose we have two implementations of the same instruction set architecture.
Computer A has a clock cycle time of 250ps and a CPI of 2.0 for some program,
and computer B has a clock cycle time of 500ps and a CPI of 1.2 for the same
program. Which computer is faster for this program and by how much?
- 500ps/instruction for A, 600ps/instruction for B => A is faster





1.6 Our favorite program runs in 10 seconds on computer A, which has a 2GHz
clock. We are trying to help a computer designer build a computer, B, which will
run this program in 6 seconds. The designer has determined that a substantial
increase in the clock rate is possible, but this increase will affect the rest of the
CPU design, causing computer B to require 1.2 times as many clock cycles as
computer A for this program. What clock rate should we tell the designer to
target?
- Program takes 20G-cycles on A. It will take 24G-cycles on B.
- clock rate = 24G-cycles/6sec = 4GHz




1.6 If computer A runs a program in 10 seconds and computer B runs the same
program in 15 seconds, how much faster is A than B?
- SpeedA = 1/10, SpeedB = 1/15
- SpeeadA/SpeedB = 1.5




1.6 Do the following changes to a computer system increase throughput, decrease
response time, or both?
  1. Replacing the processor in a computer with a faster version
  2. Adding additional processors to a system that uses multiple processors
for separate tasks—for example, searching the web

- 1 would help decrease response time and increase throughput
- 2 would only increase throughput




1.5 A key factor in determining the cost of an integrated circuit is volume. Which of
the following are reasons why a chip made in high volume should cost less?

- With high volumes, the manufacturing process can be tuned to a particular
design, increasing the yield.
- The masks used to make the chip are expensive, so the cost per chip is lower
for higher volumes.
- Engineering development costs are high and largely independent of volume;
thus, the development cost per die is lower with high-volume parts.


1.4: Semiconductor DRAM memory, flash memory, and disk storage differ
significantly. For each technology, list its volatility, approximate relative
access time, and approximate relative cost compared to DRAM.

```
                  DRAM             flash memory      disk
volatility       volatile        non-volatile     non-volatile           
access time      fast                medium        slow
cost              DRAM            cheaper than DRAM   cheaper than flash
```
