# Understanding SystemVerilog Datatypes

## Datatypes
- Handle hardware
  - reg (popular in procedural)
  - wire (popular in continous)
- Add a variable
  - fixed point
    - 2 state: 0,1
      - signed: 8-bit byte, 16-bit shortint, 32-bit int, 64-bit longint
      - unsigned: bit[7:0], bit[15:0], bit[31:0] = int unsigned
    - 4 state: 0,1,x,z: integer = 32-bit signed
  - floating point (real: 64 bit double precision)
- For simulation
  - Fixed point time: time -> 64-bit
  - Float point time: reatltime -> 64 bit
