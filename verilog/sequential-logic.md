# Designing Sequential Logic

## Clock, D-Latch, and D Flip-Flop

D flip-flops are used for:
- Pipelining (dividing bigger blocks into smaller sections to increase throughput)
- Synchronization
- Avoid glitches/hazards
- Clock frequency
- Isolate
- Sleep mode

## D FFs vs D-latch

D-latch
- Level sensitive device

DFF
- Edge triggered

## D-Latch (Dataflow)
```
module dlatch_df(q,d,en);
  input en,d;
  output q;

  assign q = en?d:q;
endmodule
```

## D-Latch (Behavioral)
```
module dlatch_bh(q,d,en);
  input en,d;
  output reg q;

  always @(en,q)
    if (en) q = d;
endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0c37c1a9-d7ed-4e10-84f9-b79f1b4a237a)

## D Latch with Asynch Reset (Behavioral)
```
module dlatch_bh(q,d,en,rst);
  input en,d,rst;
  output reg q;

  always @(en,q,rst)
    if(rst)
      q = 1'b0;
    else if(en)
      q = d;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/195b9e6a-b879-4746-b95a-1acb42aa9acc)

## DFF (Basic)
```
module dffb(q,d,clk);
  input d,clk;
  output reg q;

  always @(posedge clk)
    if(clk)
      q <= d; // non-blocking assignment operator. = is blocking
endmodule
```

Blocking statements:
```
// These statements execute in order
a = b;
c = a;
d = c;

// They are equal to this statement:
d = b;
```

Non-blocking statements:
```
// These are concurrent statements
a <= b;
c <= a;
d <= c;
```

We will never use blocking statements to implement a DFF.

## Positive edge triggered D flip-flop with asynch active high reset
```
module dff_Pe_Ar(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always @(posedge clk or posedge rst)
    if (rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

## Negative edge triggered D flip-flop with asynch active high reset
```
module dff_Ne_Ar(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always @(negedge clk or posedge rst)
    if (rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

Negative edge triggering is used a little bit more frequently for flip flops is because even a small spike would cause the FF to get triggered:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/52d8e5ff-b91e-4b13-abe8-098f42c58814)

This scenario is a lot more rare with a line thats at one.

## Positive edge triggered DFF with asynch active low reset
```
module dff_Pe_ALr(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always @(posedge clk, negedge rst)
    if (!rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

## Positive edge triggered DFF with asynch active high set
```
module dff_Pe_Alr_Ahs(q,d,clk,rst,set);
  input d,clk,rst,set;
  output reg q;

  always@(posedge clk, negedge rst, posedge set)
    if(!rst)
      q <= 1'b0;
    else if(set)
      q <= 1'b1;
    else
      q <= d;

endmodule
```

## Synch DFF with active high reset
```
module dff_Sr(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always@(posedge clk)
    if(rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

Synch reset is the recommended way of coding.

## Synch DFF with active low reset
```
module dff_Slr(q,d,clk,rst);
  input d,clk,rst;
  output reg q;

  always@(posedge clk)
    if(!rst)
      q <= 1'b0;
    else
      q <= d;

endmodule
```

Reset is usually active low in real life.

## Synch DFF with reset and set
```
module dff_Slr_Shs(q,d,clk,rst,set);
  input d,clk,rst,set;
  output reg q;

  always@(posedge clk)
    if(!rst)
      q <= 1'b0;
    else if(set)
      q <= 1'b1;
    else
      q <= d;

endmodule
```

## Synch and asynch reset design
Synch reset:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/613dc9b6-5024-41b1-b2d0-cc186f216e0c)

Asynch reset:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/132697f2-1fe1-459a-9095-ffeef7386b0b)

## 8-bit twin register set
```
module Reg_set(Q1,Q2,clk,rst,D1,D2);
  input clk,rst;
  input [7:0]D1,D2;
  output reg [7:0]Q1,Q2;

  always@(posedge clk)
    if(rst)
      begin
        Q1 <= 0;
        Q2 <= 0;
      end
    else
      begin
        Q1 <= D1;
        Q2 <= D2;
      end

endmodule
```

8 1-bit FF inside each:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/5bcfe989-0763-4a6a-a169-628f83cac5b1)

## Designing a 5-bit Left to Right shift register
```
module SR_LR(SO,clk,rst,SI);
  input SI,clk,rst;
  output SO;

  reg [4:0]SR;

  always@(posedge clk, negedge rst)  // asynch reset
    if(!rst)
      SR <= 5'd0;
    else
      SR <= {SR[3:0],SI}; // SR <= {SI,SR[4:1]} for shift right

  assign SO = SR[4];  // SO = SR[0] for shift right

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7823c959-2292-49d6-a648-25a51545b1c0)

If reset is not built in, each input will have a mux in front of its input.
```
always@(posedge clk)
  if (reset)
    SR <= 0;
  else
    begin
      // These statements can be in any order, since they are concurrent
      SR[0] <= SI;
      SR[1] <= SR[0];
      SR[2] <= SR[1];
      SR[3] <= SR[2];
      SR[4] <= SR[3];
    end
```

## Designing a 5-bit universal shift register
```
module USR(PO,SO,PI,sel,clk,rst,SI);
  input [1:0] sel;
  input [4:0] PI;
  input clk,rst,SI;
  output reg[4:0] PO;

  always@(posedge clk)
    if (rst)
      PO <= 5'd0;
    else
      begin
        case(sel)
          2'b00: PO <= PO;
          2'b01: PO <= {PO[3:0],SI};  // shift left
          2'b10: PO <= {SI,PO[4:1]};  // shift right
          2'b11: PO <= PI;
          default: PO <= 0;
        end
      end

  assign SO = (sel == 2'b01) ? PO[4] : PO[0];

endmodule
```
5 sets of FF:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f491559e-4934-4559-9fdf-066ef528a6bc)

## Designing a basic counter
```
module counter_up_basic(count,clk,rst);
  input clk,rst;
  output [7:0] count;

  reg [7:0] count_temp;

  always@(posedge clk)
    if(!rst)
      count_temp <= 8'd0;
    else
      count_temp <= count_temp + 1;

  assign count = count_temp;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/31c98be6-546a-476c-afba-543da17228a6)

## Writing a test bench for a counter
```
module counter_up_basic_tb;
  reg clk,rst;
  wire [7:0] count;

  counter_up_basic c0(.clk(clk), .rst(rst), .count(count));

  always #5 clk = ~clk;

  initial
    begin
      clk = 0;
      rst = 1;
  
      #10 rst = 0;
      #20 rst = 1;  // 30
      #100 $stop;  // 130
    end
endmodule
```

## Designing an up counter with load option
```
module counter_up_load(count,clk,load,rst,data);
  input [7:0] data;
  input clk,rst,load;
  output [7:0] count;

  reg [7:0] count_temp;

  always@(posedge clk)
    if(!rst)
      count_temp <= 8'd0;
    else if(load)
      count_temp <= data;
    else
      count_temp <= count_temp + 1;

  assign count = count_temp;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d3e4f542-73d9-415e-9607-2362d852b233)

## Designing an up or down counter
```
module counter_up_down(count,u_d,load,clk,rst,data);
  input [7:0] data;
  input clk,rst,load,u_d;
  output [7:0] count;

  reg [7:0] count_temp;

  always@(posedge clk)
    if (!rst)
      count_temp <= 8'd0;
    else if (load)
      count_temp <= data;
    else if (u_d)
      count_temp <= count_temp + 1;
    else
      count_temp <= count_temp - 1;

  assign count = count_temp;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/48028d45-f4ae-43ff-8e60-21a41838a089)

## Designing a modulus counter
MOD 47 counter
```
module counter_mod47_up(count,clk,rst,data);
  input [7:0] data;
  input clk,rst;
  output [7:0] count;

  reg [7:0] count_temp;

  always@(posedge clk)
    if(!rst | count_temp >= 8'd46) // self correcting
      count_temp <= 8'd0;
    else
      count_temp <= count_temp + 1;

  assign count = count_temp;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/76634b9f-0f03-4d1d-9f2e-e8a4c84cbed2)

## Designing a range up counter
10 to 40 counter
```
module counter_10_to_40_up(count,clk,rst,data);
  input [7:0] data;
  input clk,rst;
  output [7:0] count;

  reg [7:0] count_temp;

  always@(posedge clk)
    if(!rst | count_temp>=8'd40 | count_temp<8'd10) // self correcting
      count_temp <= 8'd10;
    else
      count_temp <= count_temp + 1;

  assign count = count_temp;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/153b198c-a59f-4560-936f-bf0bfd3d6cdf)

## Designing a range up or down counter with load option
```
module counter_10_to_40_up_down(count,u_d,load,clk,rst,data);
  input [7:0] data;
  input clk,rst;
  output [7:0] count;

  reg [7:0] count_temp;

  always@(posedge clk)
    if(!rst | count_temp > 8'd40 | count_temp < 8'd10)
      count_temp <= 8'd10;
    else if(load)
      count_temp <= data;
    else if(u_d)
      count_temp <= (count_temp >= 8'd40)?8'd10:count_temp + 1;
    else
      count_temp <= (count_temp <= 8'd10)8'd40:count_temp - 1;

  assign count = count_temp;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/440ac8e3-a5e5-4ada-864a-d6f33a0f768d)

## Designing a clock frequency divider (Divide by 2)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2a96e9c0-8b04-4db0-b67f-1b39295f51cd)

```
module freq_div_by_2(clk_out,clk,rst);
  input clk,rst;
  output reg clk_out;

  always@(posedge clk)
    if(rst)
      clk_out <= 0;
    else
      clk_out <= ~clk_out;

endmodule
```

## Designing a clock frequency divider (Divide by 4)
```
module freq_div_by_4(clk_out,clk,rst);
  input clk,rst;
  output reg clk_out;

  always@(posedge clk)
    if(rst)
      clk_div2 <= 0;
    else
      clk_div2 <= ~clk_div2;
  endmodule

  always@(posedge clk_div2)
    if(rst)
      clk_out <= 0;
    else
      clk_out <= ~ clk_out;

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ec900fbe-1cf7-4419-b051-269db3490f31)

## Designing a clock frequency divider (Divide by 3)
```
module div_3(
  input clk,
  input reset,
  output clk_out);

  reg [1:0] pos_cnt;
  reg [1:0] neg_cnt;

  always@(posedge clk)
    if(reset)
      pos_cnt <= 0;
    else if (pos_cnt == 2)
      pos_cnt <= 0;
    else
      pos_cnt <= pos_cnt + 1;

  always@(negedge clk)
    if(reset)
      neg_cnt <= 0;
    else if (neg_cnt == 2)
      neg_cnt <= 0;
    else
      neg_cnt <= neg_cnt + 1;

  assign clk_out = ((pos_cnt == 2) | (neg_cnt == 2));

endmodule
```

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/9d9f1168-1985-467b-925a-cac0ecc952b4)

## Designing a single clock first in and first out (FIFO)

Need to synchronize data transfer between M1 and M2

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/e3d5fb9e-05e8-4b59-b80f-3953e0f2e45d)

Circular buffer:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0fc9ec4d-489d-4187-b92d-dc0064a5fb98)

```
module FIFO(clk,rst,buf_in,buf_out,wr_en,rd_en,buf_empty,buf_full,fifo_counter);
  input rst,clk,wr_en,rd_en;
  input [7:0] buf_in;
  output [7:0] buf_out;
  output buf_empty, buf_full;
  output [7:0] fifo_counter;

  reg [7:0] buf_out;
  reg buf_empty, buf_full;
  reg [6:0] fifo_counter;
  reg [3:0] rd_ptr, wr_ptr;
  reg [7:0] buf_mem[63:0];

  always@(fifo_counter)
    begin
      buf_empty = (fifo_counter == 0);
      buf_full = (fifo_counter == 64);
    end

  always@(posedge clk or posedge rst)
    begin
      if(rst)
        fifo_counter <= 0;
      else if((!buf_full && wr_en) && (!buf_empty && rd_en)
        fifo_counter <= fifo_counter;
      else if(!buf_full && wr_en)
        fifo_counter <= fifo_counter + 1;
      else if(!buf_empty && rd_en)
        fifo_counter <= fifo_counter - 1;
      else
        fifo_counter <= fifo_counter;
    end

  always@(posedge clk or posedge rst)
    begin
      if(rst)
        buf_out <= 0;
      else
        begin
          if(rd_en && !buf_empty)
            buf_out <= buf_mem[rd_ptr];
          else
            buf_out <= buf_out;
        end
    end

  always@(posedge clk)
    begin
      if(wr_en && !buf_full)
        buf_mem[wr_ptr] <= buf_in;
      else
        buf_mem[wr_ptr] <= buf_mem[wr_ptr];
    end

  always@(posedge clk or posedge rst)
    begin
      if(rst)
        begin
          wr_ptr <= 0;
          rd_ptr <= 0;
        end
      else
        begin
          if(!buf_full && wr_en)
            wr_ptr <= wr_ptr + 1;
          else
            wr_ptr <= wr_ptr;
          if(!buf_empty && rd_en)
            rd_ptr <= rd_ptr + 1;
          else
            rd_ptr <= rd_ptr;
        end
    end

endmodule
```

## Designing a dual clock first in first out (FIFO)

A clock for writing and a clock for reading

```
module FIFO(clk_r,clk_w,rst,buf_in,buf_out,wr_en,rd_en,buf_empty,buf_full,fifo_counter);
  input rst,clk_r,clk_w,wr_en,rd_en;
  input [7:0] buf_in;
  output [7:0] buf_out;
  output buf_empty, buf_full;
  output [3:0] fifo_counter;

  reg [7:0] buf_out;
  reg buf_empty, buf_full;
  reg [6:0] fifo_counter;
  reg [3:0] rd_ptr, wr_ptr;
  reg [7:0] buf_mem[63:0];

  always@(fifo_counter)
    begin
      buf_empty = (fifo_counter==0);
      buf_full = (fifo_counter==64);
    end

  always@(posedge clk_w or posedge rst)
    begin
      if(rst)
        fifo_counter <= 0;
      else if(!buf_full && wr_en)
        fifo_counter <= fifo_counter + 1;
      else
        fifo_counter <= fifo_counter;
    end

  always@(posedge clk_r)
    begin
      if(!buf_empty && rd_en)
        fifo_counter <= fifo_counter - 1;
      else
        fifo_counter <= fifo_counter;
    end

  always@(posedge clk_w)
    begin
      if(rst)
        buf_out <= 0;
      else
        begin
          if(rd_en && !buf_empty)
            buf_out <= buf_mem[rd_ptr];
          else
            buf_out <= buf_out;
        end
    end

  always@(posedge clk_w)
    begin
      if(wr_en && !buf_full)
        buf_mem[wr_ptr] <= buf_in;
      else
        buf_mem[wr_ptr] <= buf_mem[wr_ptr];
    end

  always@(posedge clk_r or posedge rst)
    begin
      if(rst)
        rd_ptr <= 0;
      else if(!buf_empty && rd_en)
        rd_ptr <= rd_ptr + 1;
      else
        rd_ptr <= rd_ptr;
    end
  end

  always@(posedge clk_r or posedge rst)
    begin
      if(rst)
        rd_ptr <= 0;
      else if(!buf_empty && rd_en)
        rd_ptr <= rd_ptr + 1;
      else
        rd_ptr <= rd_ptr;
    end
  end

endmodule
```
