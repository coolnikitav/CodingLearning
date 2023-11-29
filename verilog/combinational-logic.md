# Designing Combinational Logic

## Valued Logic
Verilog has 4-valued logic: 0, 1, X, Z

0: 
- Logic zero (a = 0)
- Strong zero (line that can ground everything on that line)
- False case
- Low state

1:
- Logic one (a = 1)
- Strong one (line that can pull everything on that line to Vdd)
- True case
- High state

X (does not occur in real life, we just don't know whether the value is 1 or 0. It is mainly for simulation purposes):
- Unknown (an input is unknown, and output cannot be determined)
- Conflict (two people writing different values to the same line. Happens often in simulation)
- Metastability (for example, setup or hold times are violated in a FF)
- Uninitialized (mostly for FF, clock hasnt arrived, before first clock)

Z:
- High impedance (see in tri state buffers. It has an enable, input A, and output Y. When E = 1, Y = A. When E = 0, Y = 'Z'. Means nothing is driven on this line, like a free disconnected wire, no voltage).

VHDL has 9 values.

## Data types
2 major data types:

wire
 - default input, output
 - need to explicitely declare wire is when you use structural. For example, between a module and a gate (between modules and primitives). Need to name wires n1,n2...

reg
 - Only used in behavioral blocks: always, initial
