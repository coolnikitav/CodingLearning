# Projects

## 8:1 MUX
```
module mux(
  input a,b,c,d,e,f,g,h,
  input [2:0] sel,
  output reg y
);
  always @(*) begin
    case(sel)
      0: y = a;
      1: y = b;
      2: y = c;
      3: y = d;
      4: y = e;
      5: y = f;
      6: y = g;
      7: y = h;
      default: y = 0;
    endcase
  end
endmodule

module tb;
  reg a,b,c,d,e,f,g,h;
  reg [2:0] sel;
  wire y;
  
  mux dut (a,b,c,d,e,f,g,h,sel,y);
  
  covergroup cvr_mux;
    option.per_instance = 1;
    coverpoint a {
      bins a_lo = {0};
      bins a_hi = {1};
    }
    coverpoint b {
      bins b_lo = {0};
      bins b_hi = {1};
    }
    coverpoint c {
      bins c_lo = {0};
      bins c_hi = {1};
    }
    coverpoint d {
      bins d_lo = {0};
      bins d_hi = {1};
    }
    coverpoint e {
      bins e_lo = {0};
      bins e_hi = {1};
    }
    coverpoint f {
      bins f_lo = {0};
      bins f_hi = {1};
    }
    coverpoint g {
      bins g_lo = {0};
      bins g_hi = {1};
    }
    coverpoint h {
      bins h_lo = {0};
      bins h_hi = {1};
    }
    coverpoint sel {
      bins sel_val[] = {[0:7]};
    }
    coverpoint y;
    cross_a_sel:cross sel, a {
      ignore_bins sel_other = binsof(sel) intersect {[1:7]};
    }
    cross_b_sel:cross sel, b {
      ignore_bins sel_other = binsof(sel) intersect {0, [2:7]};
    }
    cross_c_sel:cross sel, c {
      ignore_bins sel_other = binsof(sel) intersect {[0:1], [3:7]};
    }
    cross_d_sel:cross sel, d {
      ignore_bins sel_other = binsof(sel) intersect {[0:2], [4:7]};
    }
    cross_e_sel:cross sel, e {
      ignore_bins sel_other = binsof(sel) intersect {[0:3], [5:7]};
    }
    cross_f_sel:cross sel, f {
      ignore_bins sel_other = binsof(sel) intersect {[0:4], [6:7]};
    }
    cross_g_sel:cross sel, g {
      ignore_bins sel_other = binsof(sel) intersect {[0:5], 7};
    }
    cross_h_sel:cross sel, h {
      ignore_bins sel_other = binsof(sel) intersect {[0:6]};
    }
  endgroup
  
  initial begin
    cvr_mux ci = new();
    
    for (int i = 0; i < 50; i++) begin
      {a,b,c,d,e,f,g,h} = $urandom();
      sel = $urandom();
      ci.sample();
      #1;
    end
  end
endmodule

#     COVERGROUP COVERAGE
#     ==================================================================
#     |          Covergroup           |   Hits   |  Goal /  |  Status  |
#     |                               |          | At Least |          |
#     ==================================================================
#     | TYPE /tb/cvr_mux              | 100.000% | 100.000% | Covered  |
#     ==================================================================
#     | INSTANCE <UNNAMED1>           | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::a      | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin a_lo                      |       32 |        1 | Covered  |
#     | bin a_hi                      |       18 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::b      | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin b_lo                      |       22 |        1 | Covered  |
#     | bin b_hi                      |       28 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::c      | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin c_lo                      |       22 |        1 | Covered  |
#     | bin c_hi                      |       28 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::d      | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin d_lo                      |       23 |        1 | Covered  |
#     | bin d_hi                      |       27 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::e      | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin e_lo                      |       29 |        1 | Covered  |
#     | bin e_hi                      |       21 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::f      | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin f_lo                      |       25 |        1 | Covered  |
#     | bin f_hi                      |       25 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::g      | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin g_lo                      |       33 |        1 | Covered  |
#     | bin g_hi                      |       17 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::h      | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin h_lo                      |       23 |        1 | Covered  |
#     | bin h_hi                      |       27 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::sel    | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin sel_val[0]                |        8 |        1 | Covered  |
#     | bin sel_val[1]                |        4 |        1 | Covered  |
#     | bin sel_val[2]                |        9 |        1 | Covered  |
#     | bin sel_val[3]                |        6 |        1 | Covered  |
#     | bin sel_val[4]                |        7 |        1 | Covered  |
#     | bin sel_val[5]                |        5 |        1 | Covered  |
#     | bin sel_val[6]                |        6 |        1 | Covered  |
#     | bin sel_val[7]                |        5 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::y      | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin auto[0]                   |       25 |        1 | Covered  |
#     | bin auto[1]                   |       24 |        1 | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_a_sel | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin <sel_val[0],a_lo>         |        5 |        1 | Covered  |
#     | bin <sel_val[0],a_hi>         |        3 |        1 | Covered  |
#     | ignore bin sel_other          |       42 |    -     | Occurred |
#     |-------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_b_sel | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin <sel_val[1],b_lo>         |        2 |        1 | Covered  |
#     | bin <sel_val[1],b_hi>         |        2 |        1 | Covered  |
#     | ignore bin sel_other          |       46 |    -     | Occurred |
#     |-------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_c_sel | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin <sel_val[2],c_lo>         |        3 |        1 | Covered  |
#     | bin <sel_val[2],c_hi>         |        6 |        1 | Covered  |
#     | ignore bin sel_other          |       41 |    -     | Occurred |
#     |-------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_d_sel | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin <sel_val[3],d_lo>         |        4 |        1 | Covered  |
#     | bin <sel_val[3],d_hi>         |        2 |        1 | Covered  |
#     | ignore bin sel_other          |       44 |    -     | Occurred |
#     |-------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_e_sel | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin <sel_val[4],e_lo>         |        3 |        1 | Covered  |
#     | bin <sel_val[4],e_hi>         |        4 |        1 | Covered  |
#     | ignore bin sel_other          |       43 |    -     | Occurred |
#     |-------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_f_sel | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin <sel_val[5],f_lo>         |        3 |        1 | Covered  |
#     | bin <sel_val[5],f_hi>         |        2 |        1 | Covered  |
#     | ignore bin sel_other          |       45 |    -     | Occurred |
#     |-------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_g_sel | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin <sel_val[6],g_lo>         |        4 |        1 | Covered  |
#     | bin <sel_val[6],g_hi>         |        2 |        1 | Covered  |
#     | ignore bin sel_other          |       44 |    -     | Occurred |
#     |-------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_h_sel | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin <sel_val[7],h_lo>         |        2 |        1 | Covered  |
#     | bin <sel_val[7],h_hi>         |        3 |        1 | Covered  |
#     | ignore bin sel_other          |       45 |    -     | Occurred |
#     ==================================================================
```

## Priority Encoder
```
module penc(
  input [7:0] y,
  output reg [2:0] a
);
  always @(y) begin
    casez(y)
      8'b0000_0001: a = 3'b000;
      8'b0000_001?: a = 3'b001;
      8'b0000_01??: a = 3'b010;
      8'b0000_1???: a = 3'b011;
      8'b0001_????: a = 3'b100;
      8'b001?_????: a = 3'b101;
      8'b01??_????: a = 3'b110;
      8'b1???_????: a = 3'b111;
      default: a = 3'bzzz;
    endcase
  end
endmodule

module tb;
  reg [7:0] y;
  wire [2:0] a;
  
  penc dut (y, a);
  
  covergroup c;
    option.per_instance = 1;
    coverpoint y {
      bins zero = {8'b0000_0001};
      wildcard bins one   = {8'b0000_001?};
      wildcard bins two   = {8'b0000_01??};
      wildcard bins three = {8'b0000_1???};
      wildcard bins four  = {8'b0001_????};
      wildcard bins five  = {8'b001?_????};
      wildcard bins six   = {8'b01??_????};
      wildcard bins seven = {8'b1???_????};
    }
    coverpoint a;
  endgroup
  
  initial begin
    c ci = new();
    
    for (int i = 0; i < 500; i++) begin
      y = $urandom();
      ci.sample();
      #5;
    end
  end
endmodule

#     COVERGROUP COVERAGE
#     ============================================================
#     |        Covergroup        |   Hits   |  Goal /  | Status  |
#     |                          |          | At Least |         |
#     ============================================================
#     | TYPE /tb/c               | 100.000% | 100.000% | Covered |
#     ============================================================
#     | INSTANCE <UNNAMED1>      | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::y | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | bin zero                 |        1 |        1 | Covered |
#     | bin one                  |        4 |        1 | Covered |
#     | bin two                  |       12 |        1 | Covered |
#     | bin three                |       19 |        1 | Covered |
#     | bin four                 |       25 |        1 | Covered |
#     | bin five                 |       64 |        1 | Covered |
#     | bin six                  |      130 |        1 | Covered |
#     | bin seven                |      243 |        1 | Covered |
#     |--------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::a | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | bin auto[0]              |        1 |        1 | Covered |
#     | bin auto[1]              |        4 |        1 | Covered |
#     | bin auto[2]              |       12 |        1 | Covered |
#     | bin auto[3]              |       19 |        1 | Covered |
#     | bin auto[4]              |       25 |        1 | Covered |
#     | bin auto[5]              |       64 |        1 | Covered |
#     | bin auto[6]              |      130 |        1 | Covered |
#     | bin auto[7]              |      242 |        1 | Covered |
#     ============================================================
```

## FIFO
![image](https://github.com/user-attachments/assets/4e4ec591-99b1-48e5-9183-a1ff71326fb2)

```
module FIFO(
  input clk, rst, wr, rd,
  input [7:0] din,
  output reg [7:0] dout,
  output empty, full
);
  reg [3:0] wptr = 0, rptr = 0;
  reg [4:0] cnt = 0;
  reg [7:0] mem [15:0];
  
  always @(posedge clk) begin
    if (rst == 1'b1) begin
      wptr 		<= 0;
      rptr 		<= 0;
      cnt  		<= 0;
    end else if (wr && !full) begin
      mem[wptr] <= din;
      wptr	    <= wptr + 1;
      cnt  	    <= cnt + 1;
    end else if (rd && !empty) begin
      dout 		<= mem[rptr];
      rptr 		<= rptr + 1;
      cnt  		<= cnt - 1;
    end
  end
  
  assign empty = (cnt == 0);
  assign full  = (cnt == 16);
endmodule

module tb;
  reg        clk  = 0;
  reg        wr   = 0;
  reg        rd   = 0;
  reg        rst  = 0;
  reg  [7:0] din = 0;
  wire [7:0] dout;
  wire       empty;
  wire       full;
  
  FIFO dut (clk, rst, wr, rd, din, dout, empty, full);
  
  always #5 clk = ~clk;
  
  task write();
    for (int i = 0; i < 20; i++) begin
      wr = 1'b1;
      rd = 1'b0;
      din = $urandom();
      @(posedge clk);
      $display("wr: %0d, addr: %0d, din: %0d, full: %0d", wr, i, din, full);
      wr = 1'b0;
      @(posedge clk);
    end
  endtask
  
  task read();
    for (int i = 0; i < 20; i++) begin
      wr = 1'b0;
      rd = 1'b1;
      din = 0;
      @(posedge clk);
      rd = 1'b0;
      @(posedge clk);
      $display("rd: %0d, addr: %0d, dout: %0d, empty: %0d", rd, i, dout, empty);
    end
  endtask
  
  initial begin
    rst = 1;
    wr = 0;
    rd = 0;
    repeat(5) @(posedge clk);
    rst = 0;
    write();
    read();
  end
  
  covergroup c @(posedge clk);
    option.per_instance = 1;
    coverpoint empty {
      bins empty_l = {0};
      bins empty_h = {1};
    }
    coverpoint full {
      bins full_l = {0};
      bins full_h = {1};
    }
    coverpoint rst {
      bins rst_l = {0};
      bins rst_h = {1};
    }
    coverpoint wr {
      bins wr_l = {0};
      bins wr_h = {1};
    }
    coverpoint rd {
      bins rd_l = {0};
      bins rd_h = {1};
    }
    coverpoint din {
      bins lower = {[0:84]};
      bins mid   = {[85:169]};
      bins high  = {[170:255]};
    }
    coverpoint dout {
      bins lower = {[0:84]};
      bins mid   = {[85:169]};
      bins high  = {[170:255]};
    }
    cross_rst_wr: cross rst, wr {
      ignore_bins unused_rst   = binsof(rst)   intersect {1};
      ignore_bins unused_wr    = binsof(wr)    intersect {0};
    }
    cross_rst_rd: cross rst, rd {  
      ignore_bins unused_rst   = binsof(rst)   intersect {1};
      ignore_bins unused_rd    = binsof(rd)    intersect {0};
    }
    cross_wr_din: cross rst, wr, din {
      ignore_bins unused_rst   = binsof(rst)   intersect {1};
      ignore_bins unused_wr    = binsof(wr)    intersect {0};
    }
    cross_rd_dout: cross rst, rd, dout {
      ignore_bins unused_rst   = binsof(rst)   intersect {1};
      ignore_bins unused_rd    = binsof(rd)    intersect {0};
    }
    cross_wr_full: cross rst, wr, full {
      ignore_bins unused_rst   = binsof(rst)   intersect {1};
      ignore_bins unused_wr    = binsof(wr)    intersect {0};
      ignore_bins unused_full  = binsof(full)  intersect {0};
    }
    cross_rd_empty: cross rst, rd, empty {
      ignore_bins unused_rst   = binsof(rst)   intersect {1};
      ignore_bins unused_rd    = binsof(rd)    intersect {0};
      ignore_bins unused_empty = binsof(empty) intersect {0};
    }
  endgroup
  
  initial begin
    c ci = new();
    #1200;
    $finish();
  end
endmodule

#     COVERGROUP COVERAGE
#     =====================================================================
#     |            Covergroup            |   Hits   |  Goal /  |  Status  |
#     |                                  |          | At Least |          |
#     =====================================================================
#     | TYPE /tb/c                       | 100.000% | 100.000% | Covered  |
#     =====================================================================
#     | INSTANCE <UNNAMED1>              | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::empty     | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin empty_l                      |       70 |        1 | Covered  |
#     | bin empty_h                      |       50 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::full      | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin full_l                       |      110 |        1 | Covered  |
#     | bin full_h                       |       10 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::rst       | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin rst_l                        |      115 |        1 | Covered  |
#     | bin rst_h                        |        5 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::wr        | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin wr_l                         |      100 |        1 | Covered  |
#     | bin wr_h                         |       20 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::rd        | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin rd_l                         |      100 |        1 | Covered  |
#     | bin rd_h                         |       20 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::din       | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin lower                        |       96 |        1 | Covered  |
#     | bin mid                          |        8 |        1 | Covered  |
#     | bin high                         |       16 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::dout      | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin lower                        |       14 |        1 | Covered  |
#     | bin mid                          |        4 |        1 | Covered  |
#     | bin high                         |       56 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_rst_wr   | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin <rst_l,wr_h>                 |       20 |        1 | Covered  |
#     | ignore bin unused_rst            |        5 |    -     | Occurred |
#     | ignore bin unused_wr             |      100 |    -     | Occurred |
#     |----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_rst_rd   | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin <rst_l,rd_h>                 |       20 |        1 | Covered  |
#     | ignore bin unused_rst            |        5 |    -     | Occurred |
#     | ignore bin unused_rd             |      100 |    -     | Occurred |
#     |----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_wr_din   | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin <rst_l,wr_h,lower>           |        8 |        1 | Covered  |
#     | bin <rst_l,wr_h,mid>             |        4 |        1 | Covered  |
#     | bin <rst_l,wr_h,high>            |        8 |        1 | Covered  |
#     | ignore bin unused_rst            |        5 |    -     | Occurred |
#     | ignore bin unused_wr             |      100 |    -     | Occurred |
#     |----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_rd_dout  | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin <rst_l,rd_h,lower>           |        7 |        1 | Covered  |
#     | bin <rst_l,rd_h,mid>             |        2 |        1 | Covered  |
#     | bin <rst_l,rd_h,high>            |       10 |        1 | Covered  |
#     | ignore bin unused_rd             |       55 |    -     | Occurred |
#     |----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_wr_full  | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin <rst_l,wr_h,full_h>          |        4 |        1 | Covered  |
#     | ignore bin unused_rst            |        5 |    -     | Occurred |
#     | ignore bin unused_wr             |      100 |    -     | Occurred |
#     | ignore bin unused_full           |      110 |    -     | Occurred |
#     |----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_rd_empty | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin <rst_l,rd_h,empty_h>         |        4 |        1 | Covered  |
#     | ignore bin unused_rst            |        5 |    -     | Occurred |
#     | ignore bin unused_rd             |      100 |    -     | Occurred |
#     | ignore bin unused_empty          |       70 |    -     | Occurred |
#     =====================================================================
```

## Usage of Transition Bins: Serial Peripheral Interface
![image](https://github.com/user-attachments/assets/10b96bea-1fae-481c-919c-79356139f092)

```
module dac(input clk,
  input [11:0] din,
  input start,
  output reg mosi, cs
);
  
typedef enum {idle = 0, init = 1, send = 3, data_gen = 2, cont= 4} state_type;
state_type state;
 
reg [31:0] setup   = 32'h08000001;
reg [31:0] dac_data = 32'h00000000;
integer count = 0;
 
  always@(posedge clk) begin
	case(state)  
      idle: begin
        cs   <= 1'b1;
        mosi <= 1'b0;
        if(start)
        	state <= init;
        else
        	state <= idle;
      end
      init: begin
        if(count < 32) begin
          count <= count + 1;
          mosi  <= setup[31 - count];
          cs    <= 1'b0;
          state <= init;
        end else begin
          cs    <= 1'b1;
          count <= 0;
          state <= data_gen;
        end
      end 
      data_gen: begin
        dac_data <= {12'h030,din,8'h00};
        state    <= send;
      end 
      send: begin
        if(count < 32) begin
          count <= count + 1;
          mosi  <= dac_data[31 - count];
          cs    <= 1'b0;
          state <= send;
        end else begin
          cs    <= 1'b1;
          count <= 0;
          state <= cont;
        end
      end 
      cont: begin
        if(start)
        	state <= data_gen;
        else
        	state <= idle;
      end
	endcase
  end
endmodule

module tb;
  reg clk = 0;
  reg start = 0;
  reg [11:0] din;
  wire mosi;
  wire cs;
  
  dac dut (clk, din, start, mosi, cs);
  
  always #5 clk = ~clk;
  
  initial begin
    #20;
    start = 1;
    #1000;
    start = 0;
  end
  
  initial begin
    for (int i = 0; i < 200; i++) begin
      @(posedge clk);
      din = $urandom();
    end
  end
  
  covergroup c @(posedge clk);
    option.per_instance = 1;
    coverpoint dut.state {
      bins out_of_idle = (dut.idle => dut.init);
      bins setup_data_send = (dut.idle => dut.init[*33] => dut.data_gen);
      bins user_data_sned = (dut.data_gen => dut.send[*33] => dut.cont);
      bins stay_send_33 = (dut.send[*33]);
      bins stay_int_33 = (dut.init[*33]);
      bins start_deassert = (dut.send => dut.cont => dut.idle);
    }
  endgroup
  
  initial begin
    c ci = new();
    #2000;
    $finish();
  end

endmodule

#     COVERGROUP COVERAGE
#     ====================================================================
#     |            Covergroup            |   Hits   |  Goal /  | Status  |
#     |                                  |          | At Least |         |
#     ====================================================================
#     | TYPE /tb/c                       | 100.000% | 100.000% | Covered |
#     ====================================================================
#     | INSTANCE <UNNAMED1>              | 100.000% | 100.000% | Covered |
#     |----------------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::dut.state | 100.000% | 100.000% | Covered |
#     |----------------------------------|----------|----------|---------|
#     | bin out_of_idle                  |        1 |        1 | Covered |
#     | bin setup_data_send              |        1 |        1 | Covered |
#     | bin user_data_sned               |        2 |        1 | Covered |
#     | bin stay_send_33                 |        2 |        1 | Covered |
#     | bin stay_int_33                  |        1 |        1 | Covered |
#     | bin start_deassert               |        1 |        1 | Covered |
#     ====================================================================
```

## Counter
![image](https://github.com/user-attachments/assets/a212e3e1-461e-4919-ae74-d7df74f408b4)
```
module counter_8(
  input clk, rst, up, load,
  input [7:0] loadin,
  output reg [7:0] y
);
  always @(posedge clk) begin
    if (rst == 1'b1)
      y <= 8'b0000_0000;
    else if (load == 1'b1)
      y <= loadin;
    else begin
      if (up == 1'b1)
        y <= y+1;
      else 
        y <= y-1;
    end
  end
endmodule

interface counter_8_intf();
  logic clk, rst, up, load;
  logic [7:0] loadin;
  logic [7:0] y;
endinterface

class transaction; 
  rand bit [7:0] loadin;
  bit load;
  bit rst;
  bit up;  
  bit [7:0] y;  
endclass
 
 
////////////////////////
class generator;
  transaction t;
  mailbox mbx;
  event done;
  integer i;

  function new(mailbox mbx);
  this.mbx = mbx;
  endfunction

  task run();
    t = new();
    for(i =0; i< 200; i++) begin
      t.randomize;
      mbx.put(t);
      $display("[GEN]: Data send to driver");
      @(done);
    end    
  endtask
endclass
 
///////////////////////////////
class driver;
  mailbox mbx;
  transaction t;
  event done;

  virtual counter_8_intf vif;

  function new(mailbox mbx);
  this.mbx = mbx;
  endfunction

  task run();
    t= new();
    forever begin
      mbx.get(t);
      vif.loadin <= t.loadin;
      $display("[DRV] : Trigger Interface");
      @(posedge vif.clk);
      ->done; 
    end
  endtask
endclass
 
////////////////////////////////////////////
class monitor;
  virtual counter_8_intf vif;
  mailbox mbx;
  transaction t;
  
 ///////////adding coverage
  
  ///ld  rst  loaddin dout
  
  covergroup c ;
    option.per_instance = 1;
    coverpoint t.loadin {
      bins lower = {[0:84]};
      bins mid = {[85:169]};
      bins high = {[170:255]};
    }
    coverpoint t.rst {
      bins rst_low = {0};
      bins rst_high = {1};
    }
    coverpoint t.load {
      bins ld_low = {0};
      bins ld_high = {1};
    }
    coverpoint t.y {
      bins lower = {[0:84]};
      bins mid = {[85:169]};
      bins high = {[170:255]};
    }
    cross_ld_loadin : cross t.load, t.loadin {
      ignore_bins unused_ld = binsof(t.load) intersect {0}; 
    }
    cross_rst_up : cross t.rst, t.up {
      ignore_bins unused_rst = binsof(t.rst) intersect {1};
    }
    cross_rst_y : cross t.rst, t.y {
      ignore_bins unused_rst = binsof(t.rst) intersect {1};
    }
  endgroup

  function new(mailbox mbx);
    this.mbx = mbx;
    c = new();  
  endfunction

  task run();
    t = new();
    forever begin
      t.loadin = vif.loadin;
      t.y = vif.y;
      t.rst = vif.rst;
      t.up = vif.up;
      t.load = vif.load;

      c.sample();

      mbx.put(t);
      $display("[MON] : Data send to Scoreboard");
      @(posedge vif.clk);
    end
  endtask
endclass  
 
///////////////////////////////////////////////////
class scoreboard;
  mailbox mbx;
  transaction t;
  bit [7:0] temp; 

  function new(mailbox mbx);
  	this.mbx = mbx;
  endfunction

  task run();
    t = new();
    forever begin
    	mbx.get(t);
    end
  endtask
endclass  
 
 
/////////////////////////////////////////////////
class environment;
  generator gen;
  driver drv;
  monitor mon;
  scoreboard sco;

  virtual counter_8_intf vif;

  mailbox gdmbx;
  mailbox msmbx;

  event gddone;

  function new(mailbox gdmbx, mailbox msmbx);
    this.gdmbx = gdmbx;
    this.msmbx = msmbx;

    gen = new(gdmbx);
    drv = new(gdmbx);

    mon = new(msmbx);
    sco = new(msmbx);
  endfunction

  task run();
    gen.done = gddone;
    drv.done = gddone;

    drv.vif = vif;
    mon.vif = vif;

    fork 
      gen.run();
      drv.run();
      mon.run();
      sco.run();
    join_any;
  endtask
endclass
 
/////////////////////////////////////
 
module tb();
 
  environment env;

  mailbox gdmbx;
  mailbox msmbx;

  counter_8_intf vif();

  counter_8 dut ( vif.clk, vif.rst, vif.up, vif.load,  vif.loadin, vif.y );

  always #5 vif.clk = ~vif.clk;

  initial begin
   vif.clk = 0;
   vif.rst = 1;
   #50; 
   vif.rst = 0;  
  end

  initial begin
  	#60;
    repeat(20) begin
     vif.load = 1;
     #10;
      vif.load = 0;
     #100;
    end
  end

   initial begin
  	#60;
    repeat(20) begin
      vif.up = 1;
      #70;
      vif.up = 0;
      #70;
    end
  end 

  initial begin
    gdmbx = new();
    msmbx = new();
    env = new(gdmbx, msmbx);
    env.vif = vif;
    env.run();
    #2000;
    $finish;
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;  
  end
endmodule

#     COVERGROUP COVERAGE
#     ======================================================================
#     |            Covergroup             |   Hits   |  Goal /  |  Status  |
#     |                                   |          | At Least |          |
#     ======================================================================
#     | TYPE /monitor/c                   | 100.000% | 100.000% | Covered  |
#     ======================================================================
#     | INSTANCE <UNNAMED1>               | 100.000% | 100.000% | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::t.loadin   | 100.000% | 100.000% | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | bin lower                         |       73 |        1 | Covered  |
#     | bin mid                           |      262 |        1 | Covered  |
#     | bin high                          |       65 |        1 | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::t.rst      | 100.000% | 100.000% | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | bin rst_low                       |      394 |        1 | Covered  |
#     | bin rst_high                      |        6 |        1 | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::t.load     | 100.000% | 100.000% | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | bin ld_low                        |      380 |        1 | Covered  |
#     | bin ld_high                       |       20 |        1 | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::t.y        | 100.000% | 100.000% | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | bin lower                         |      154 |        1 | Covered  |
#     | bin mid                           |      198 |        1 | Covered  |
#     | bin high                          |       48 |        1 | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::t.up       | 100.000% | 100.000% | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | bin auto[0]                       |      260 |        1 | Covered  |
#     | bin auto[1]                       |      140 |        1 | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_ld_loadin | 100.000% | 100.000% | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | bin <ld_high,lower>               |        8 |        1 | Covered  |
#     | bin <ld_high,mid>                 |        7 |        1 | Covered  |
#     | bin <ld_high,high>                |        5 |        1 | Covered  |
#     | ignore bin unused_ld              |      380 |    -     | Occurred |
#     |-----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_rst_up    | 100.000% | 100.000% | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | bin <rst_low,auto[0]>             |      254 |        1 | Covered  |
#     | bin <rst_low,auto[1]>             |      140 |        1 | Covered  |
#     | ignore bin unused_rst             |        6 |    -     | Occurred |
#     |-----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::cross_rst_y     | 100.000% | 100.000% | Covered  |
#     |-----------------------------------|----------|----------|----------|
#     | bin <rst_low,lower>               |      148 |        1 | Covered  |
#     | bin <rst_low,mid>                 |      198 |        1 | Covered  |
#     | bin <rst_low,high>                |       48 |        1 | Covered  |
#     | ignore bin unused_rst             |        6 |    -     | Occurred |
#     ======================================================================
```
