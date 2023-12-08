# Designing Memories

## Memory array options and definitions

Verilog synthesis mainly supports synchronous memories. So your memories need a clock to read and write.

If the memory is asynchronous, it will need a wrapper.

Direct synthesis is only possible for DFF based SRAMs.

```
reg [7:0] ram;  // word size here is 1 byte - 8 bits
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/5ede44a7-b4cf-474c-8d93-c9b18c453895)

```
reg ram[7:0];  // 1 bit word size, 8 of them
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7379bf3f-af97-412b-83e9-0af5c6c4b1a6)

```
reg ram[7:0][0:7];  // 2D memory. word size is 1 bit
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/fde82612-210f-4f38-ad91-2ac663f38b8a)

```
reg [7:0] ram[0:3];  // word size is 1 byte, there are 4 such bytes
// Cannot access individual bits, can only access rows
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f0ebf199-0429-4787-b96f-8d58783412c9)

```
reg [7:0] ram[0:1023];
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f6dd9910-dfe7-4df0-aac4-595ba8728d38)

```
reg [3:0] ram[0:3][0:4];  // word size is 4 bits
// Cannot access individual bits, only the 4 bit words
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/6e482530-bfba-4114-aa5d-3832ad12c978)

## Single port ram - v1
```
module ram_single_port1(
  output reg [7:0] q,
  input [7:0] data,
  input [5:0] read_adder, write_adder,
  input we, clk
  );
  reg [7:0] ram[63:0];

  always@(posedge clk)
    begin
      if(we)
        ram[write_adder] <= data;
      q <= ram[read_adder];
    end

endmodule
```

If read_addr == write_addr, we will fetch the old value and then write the new one.

You can only do one read, one write, or one read and one write at a time. That is why it is called single port ram.

## Single port ram - v2
```
module ram_single_port2(
  output reg [7:0] q,
  input [7:0] data,
  input [5:0] read_addr, write_addr,
  input we, clk
  );
  reg [7:0] ram[63:0];

  always@(posedge clk)
    begin
      if(we)
        /* using blocking statements
         * if write_addr == read_addr and we want to fetch the new data
         * this way new data gets written and then read */
        ram[write_addr] = data;  
      q = ram[read_addr];
    end

endmodule
```

## Single port ram - v3
```
module ram_single_port3(
  output [7:0] q,
  input [7:0] data,
  input [5:0] addr,
  input we, clk
  );
  reg [7:0] ram[63:0];
  reg [5:0] addr_reg;

  always@(posedge clk)
    begin
      if (we)
        ram[addr] <= data;
      addr_reg <= addr;
    end

  // read new data
  assign q = ram[addr_reg];

endmodule
```

## Single port ram - v4
```
module ram_single_port4(
  output [7:0] q,
  input [7:0] data,
  input [5:0] read_addr, write_addr,
  input we, clk
  );

  reg [7:0] ram[63:0];
  reg [5:0] read_addr_reg;

  // new data read & addr registered
  always@(posedge clk)
    begin
      if(we)
        ram[write_addr] <= data;
      read_addr_reg <= read_addr;
    end

  assign q = ram[read_addr_reg];

endmodule
```

## Dual port ram - v1
Not a true dual port RAM. It can only write using port 1 and read using port 2. Port 1 cannot read and port 2 cannot write.

If read while write happens, behavior is difficult to predict.
```
module ram_dual_port1(
  output reg [7:0] q,
  input [7:0] data,
  input [5:0] read_addr, write_addr,
  input we, read_clk, write_clk
  );
  reg [7:0] ram[63:0];

  // write port
  always@(posedge write_clk)
    if(we)
      ram[write_addr] <= data;

  // read port
  always@(posedge read_clk)
    q <= ram[read_addr];

endmodule
```

## Dual port ram - v2
```
module ram_dual_port2(
  output reg [7:0] q,
  input [7:0] data,
  input [5:0] read_addr, write_addr,
  input we, read_clk, write_clk
  );

  reg [7:0] ram[63:0];
  reg [5:0] read_addr_reg;

  // write port
  always@(posedge write_clk)
    if(we)
      ram[write_addr] <= data;

  // read port
  always@(posedge read_clk)
    begin
      q <= ram[read_addr_reg];
      read_addr_reg <= read_addr;
    end

endmodule
```

## True dual port ram - v1

2 ports (a,b) that are both capable of reading and writing
```
module ram_true_dual_port1(
  output reg [7:0] q_a, q_b,
  input [7:0] data_a, data_b,
  input [5:0] addr_a, addr_b,
  input we_a, we_b, clk
  );

  reg [7:0] ram[63:0];

  // port_a
  always@(posedge clk)
    if(we_a)
      begin
        ram[addr_a] <= data_a;
        q_a <= data_a;
      end
    else
      q_a <= ram[addr_a];

  // port_b
  always@(posedge clk)
    if (we_b)
      begin
        ram[addr_b] <= data_b;
        q_b <= data_b;
      end
    else
      q_b <= ram[addr_b];

endmodule
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/194bc29f-a8bf-4a98-a957-5e47bb95c39a)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/82a55a65-7817-47a6-858e-572c4aa1168d)

## True dual port ram - v2
Allows simultaneous reading and writing
```
module ram_true_dual_port2(
  output reg [7:0] q_a, q_b,
  input [7:0] data_a, data_b,
  input [5:0] addr_a, addr_b,
  input we_a, we_b, clk
  );

  reg [7:0] ram[63:0];

  //port_a
  always@(posedge clk)
    if(we_a)
      ram[addr_a] <= data_a;
    q_a <= ram[addr_a];

  //port_b
  always@(posedge clk)
    if(we_b)
      ram[addr_b] <= data_b;
    q_b <= ram[addr_b];

endmodule
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a1cfc38a-aff2-4b9b-a2c9-ab673aab6cff)
