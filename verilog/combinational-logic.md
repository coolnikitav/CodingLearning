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

## Number Representation
When you defined a number, the default size is 32 bit binary.

<size><base><number>

- Decimal (default) -> 10'd8 (0000001000)
- Hex -> 9'hfe (011111110)
- Binary -> 8'b1100 (00001100)
- Octal -> 7'o67 (0110111)

7'hfe (1111110) - truncates bits

Can use _ for better readibility

32'habcd_efab;

Negative numbers:

6 bit x wire = -6b'1_1011 (The num is 011011. We take 2's complement, so number stored will be 100101)

4 bit x wire = -6b'1_1011 (It will truncate 100101 to 0101 and store it in x)

8 bit x wire = -6b'1_1011 (x will store 11100101. So the number is sign extended)

Valid number (only for simulation. Cannot synthesize):

y = 5'b0_1zox

6 bit wire y = 5'bz_1011; (Gets sign extended to zz1011)

8 bit wire y = 5'bx_0011; (Gets sign extended to xxxx0011)

## Bit and bus
```
input x,y; // both are single bits

wire a,b; // both are single bits

reg c,d; // both are single bits

input [3:0]x; // bus, x[3] is MSB, x[0] is LSB
a = x[0]; // LSB of x
b = x[3]; // MSB of x

wire [1:0]w;
w = x[2:1]; 

wire [0:7]w; // w[7] is LSB, w[0] is MSB
```
## Naming Conventions
If our file name is ha.v, we want our module name to be "ha"

Module name 
 - Start with a letter (lower case)
 - Can contain numbers and underscores (full_adder_4_bit)

## Operator - Bitwise
Work on each bit of the wire

```
wire a,b,c;
wire [3:0]w,x,y;

// not - used to complement
a = ~b; // b gets inverted and flows to a
x = ~y; // each bit of y gets inverted and becomes x

// and - masking bits (for example you want to extract the last 2 bits: you apply ...00011),
// force reset (pick which bits you want to reset)
a = b & c;
x = w & y; // each bit is anded together and become x

// or - mask (set bits you want to 1),
// force set values
a = b | c;
x = w | y; // 4 or gates

// xor - selectively complement certain bits 
a = b ^ c;
x = w ^ y;

// xnor - see which bits match
a = b ~^ c;
x = w ~^ y;

// nor - force 0 and flip bits (use 1 to force 0 and 0 to flip bits)
a = b ~| c;
x = w ~| y;

// nand - force 1 and flip bits (use 0 to force 1 and 1 to flip bits)
a = b ~& c;
x = w ~& y;
```
