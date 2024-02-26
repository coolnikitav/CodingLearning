# Communication protocol: verification of serial peripheral interface

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0f635505-eb34-4285-97ce-41f7f2f1b6f7)

Master pulls the CS line low to indicate to the slave that the data is incoming.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/eede88be-fe6b-4acf-bfda-759f278c8fbc)

```
module spi(
  input clk, newd, rst,
  input [11:0] din,
  output reg sclk, cs, mosi
);
  typedef enum bit [1:0] {idle = 2'b00, enable = 2'b01, send = 2'b10, comp = 2'b11} state_type;
  state_type state = idle;
  
  int countc = 0;
  int count = 0;
  
  // generation of sclk
  always @ (posedge clk) begin
    if (rst == 1'b1) begin
      countc <= 0;
      sclk <= 1'b0;
    end
    else begin
      if (countc < 10) begin  // sclk = clk / 20
        countc <= countc + 1;
      end
      else begin
        countc <= 0;
        sclk <= ~sclk;
      end
    end
  end
  
  // state machine
  reg [11:0] temp;
  
  always @ (posedge sclk) begin
    if (rst == 1'b1) begin
      cs <= 1'b1;
      mosi <= 1'b0;
    end
    else begin
      case (state)
        idle: begin
            if (newd == 1'b1) begin
              state <= send;
              temp <= din;
              cs <= 1'b0;
            end
            else begin
              state <= idle;
              temp <= 8'h00;
            end
        end
        send: begin
            if (count < 12) begin  // sending 12 bits
              mosi <= temp[count];  // sending LSB first
              count <= count + 1;
            end
            else begin
              count <= 0;
              state <= idle;
              cs <= 1'b1;
              mosi <= 1'b0;
            end
        end
        default: state <= idle;
      endcase
    end
  end  
endmodule

interface spi_if;
  logic clk, newd, rst;
  logic [11:0] din;
  logic sclk, cs, mosi;
endinterface
```
```
///////////////////////

class transaction;
  rand bit newd;
  rand bit [11:0] din;
  bit cs;
  bit mosi;
  
  function void display(input string tag);
    $display("[%0s] : DATA_NEW : %0b DIN : %0d CS : %0b MOSI : %0b", tag, newd, din, cs, mosi);
  endfunction
  
  function transaction copy();
    copy = new();
    copy.newd = this.newd;
    copy.din = this.din;
    copy.cs = this.cs;
    copy.mosi = this.mosi;
  endfunction
endclass

///////////////////////

class generator;
  transaction trans;
  mailbox #(transaction) mbx;
  
  event done;
  event drvnext;
  event sconext;
  
  int count = 0;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
    trans = new();
  endfunction
  
  task run();
    repeat(count) begin
      assert(trans.randomize) else $error("[GEN] : Randomization failed");
      mbx.put(trans.copy);
      trans.display("GEN");
      @(drvnext);
      @(sconext);
    end
    -> done;
  endtask
endclass

///////////////////////

class driver;
  virtual spi_if sif;
  transaction trans;
  
  mailbox #(transaction) mbx;   // get data from generator
  mailbox #(bit [11:0]) mbxds;  // drv -> sco
  
  event drvnext;
  
  bit [11:0] din;
  
  function new(mailbox #(bit [11:0]) mbxds, mailbox #(transaction) mbx);
    this.mbx = mbx;
    this.mbxds = mbxds;
  endfunction
  
  task reset();
    sif.rst <= 1'b1;
    sif.cs <= 1'b1;
    sif.newd <= 1'b0;
    sif.din <= 1'b0;
    sif.mosi <= 1'b0;
    repeat(10) @(posedge sif.clk);
    sif.rst <= 1'b0;
    repeat(5) @(posedge sif.clk);
    
    $display("[DRV] : RESET DONE");
    $display("-----------------------------");
  endtask
  
  task run();
    forever begin
      mbx.get(trans);
      @(posedge sif.sclk);
      sif.newd <= 1'b1;
      sif.din = trans.din;
      mbxds.put(trans.din);
      @(posedge sif.sclk);
      sif.newd <= 1'b0;
      wait(sif.cs == 1'b1);
      $display("[DRV] : DATA SENT TO DAC : %0d", trans.din);
      -> drvnext;
    end
  endtask
endclass

///////////////////////

class monitor;
  transaction trans;
  mailbox #(bit [11:0]) mbx;  // mon -> sco
  bit [11:0] srx;  // send
  
  virtual spi_if sif;
  
  function new(mailbox #(bit [11:0]) mbx);
  	this.mbx = mbx;             
  endfunction
               
  task run();
  	forever begin
      @(posedge sif.sclk);
      wait (sif.cs == 1'b0);  // start of transaction
      @(posedge sif.sclk);
      
      for (int i = 0; i < 12; i++) begin
        @(posedge sif.sclk);
        srx[i] = sif.mosi;
      end
      
      wait(sif.cs == 1'b1);  // end of transaction
      
      $display("[MON] : DATA SENT : %0d", srx);
      mbx.put(srx);
    end
  endtask
endclass

///////////////////////

class scoreboard;
  mailbox #(bit [11:0]) mbxds, mbxms;
  bit [11:0] ds;
  bit [11:0] ms;
  event sconext;
  
  function new(mailbox #(bit [11:0]) mbxds, mailbox #(bit [11:0]) mbxms);
    this.mbxds = mbxds;
    this.mbxms = mbxms;
  endfunction
  
  task run();
    forever begin
      mbxds.get(ds);
      mbxms.get(ms);
      $display("[SCO] : DRV : %0d : MON : %0d", ds, ms);
      
      if (ds == ms)
        $display("[SCO] : DATA MATCH");
      else
        $display("[SCO] : DATA MISMATCH");
      
      $display("-----------------------------");
      -> sconext;
    end
  endtask
endclass

///////////////////////

class environment;
  generator gen;
  driver drv;
  monitor mon;
  scoreboard sco;
  
  event nextgd;
  event nextgs;
  
  mailbox #(transaction) mbxgd;
  mailbox #(bit [11:0]) mbxds;
  mailbox #(bit [11:0]) mbxms;
  
  virtual spi_if sif;
  
  function new(virtual spi_if sif);
    mbxgd = new();
    mbxms = new();
    mbxds = new();
    
    gen = new(mbxgd);
    drv = new(mbxds, mbxgd);
    
    mon = new(mbxms);
    sco = new(mbxds, mbxms);
    
    this.sif = sif;
    drv.sif = this.sif;
    mon.sif = this.sif;
    
    gen.sconext = nextgs;
    sco.sconext = nextgs;
    
    gen.drvnext = nextgd;
    drv.drvnext = nextgd;
  endfunction
  
  task pre_test();
    drv.reset();
  endtask
  
  task test();
    fork
      gen.run();
      drv.run();
      mon.run();
      sco.run();
    join_any
  endtask
  
  task post_test();
    wait(gen.done.triggered);
    $finish();
  endtask
  
  task run();
    pre_test();
    test();
    post_test();
  endtask
endclass

///////////////////////

module tb;
  spi_if sif();
  
  spi dut (.clk(sif.clk),.newd(sif.newd),.rst(sif.rst),.din(sif.din),.sclk(sif.sclk),.cs(sif.cs),.mosi(sif.mosi));
  
  initial begin
    sif.clk <= 0;
  end
  
  always #10 sif.clk <= ~sif.clk;
  
  environment env;
  
  initial begin
    env = new(sif);
    env.gen.count = 20;
    env.run();
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
endmodule
```
```
# KERNEL: [DRV] : RESET DONE
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 1 DIN : 2904 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 2904
# KERNEL: [MON] : DATA SENT : 2904
# KERNEL: [SCO] : DRV : 2904 : MON : 2904
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 974 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 974
# KERNEL: [MON] : DATA SENT : 974
# KERNEL: [SCO] : DRV : 974 : MON : 974
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 1 DIN : 510 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 510
# KERNEL: [MON] : DATA SENT : 510
# KERNEL: [SCO] : DRV : 510 : MON : 510
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 941 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 941
# KERNEL: [MON] : DATA SENT : 941
# KERNEL: [SCO] : DRV : 941 : MON : 941
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 3415 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 3415
# KERNEL: [MON] : DATA SENT : 3415
# KERNEL: [SCO] : DRV : 3415 : MON : 3415
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 974 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 974
# KERNEL: [MON] : DATA SENT : 974
# KERNEL: [SCO] : DRV : 974 : MON : 974
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 2996 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 2996
# KERNEL: [MON] : DATA SENT : 2996
# KERNEL: [SCO] : DRV : 2996 : MON : 2996
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 1 DIN : 3142 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 3142
# KERNEL: [MON] : DATA SENT : 3142
# KERNEL: [SCO] : DRV : 3142 : MON : 3142
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 1295 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 1295
# KERNEL: [MON] : DATA SENT : 1295
# KERNEL: [SCO] : DRV : 1295 : MON : 1295
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 638 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 638
# KERNEL: [MON] : DATA SENT : 638
# KERNEL: [SCO] : DRV : 638 : MON : 638
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 1 DIN : 883 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 883
# KERNEL: [MON] : DATA SENT : 883
# KERNEL: [SCO] : DRV : 883 : MON : 883
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 570 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 570
# KERNEL: [MON] : DATA SENT : 570
# KERNEL: [SCO] : DRV : 570 : MON : 570
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 1 DIN : 3482 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 3482
# KERNEL: [MON] : DATA SENT : 3482
# KERNEL: [SCO] : DRV : 3482 : MON : 3482
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 1 DIN : 727 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 727
# KERNEL: [MON] : DATA SENT : 727
# KERNEL: [SCO] : DRV : 727 : MON : 727
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 1 DIN : 2007 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 2007
# KERNEL: [MON] : DATA SENT : 2007
# KERNEL: [SCO] : DRV : 2007 : MON : 2007
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 1 DIN : 3283 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 3283
# KERNEL: [MON] : DATA SENT : 3283
# KERNEL: [SCO] : DRV : 3283 : MON : 3283
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 3894 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 3894
# KERNEL: [MON] : DATA SENT : 3894
# KERNEL: [SCO] : DRV : 3894 : MON : 3894
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 914 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 914
# KERNEL: [MON] : DATA SENT : 914
# KERNEL: [SCO] : DRV : 914 : MON : 914
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 1 DIN : 737 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 737
# KERNEL: [MON] : DATA SENT : 737
# KERNEL: [SCO] : DRV : 737 : MON : 737
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
# KERNEL: [GEN] : DATA_NEW : 0 DIN : 1887 CS : 0 MOSI : 0
# KERNEL: [DRV] : DATA SENT TO DAC : 1887
# KERNEL: [MON] : DATA SENT : 1887
# KERNEL: [SCO] : DRV : 1887 : MON : 1887
# KERNEL: [SCO] : DATA MATCH
# KERNEL: -----------------------------
```
## SPI with slave
```
module spi_master(
  input clk,newd,rst,
  input [11:0] din,
  output reg sclk,cs,mosi
);
  typedef enum bit [1:0] {idle = 2'b00, enable = 2'b01, send = 2'b10, comp = 2'b11} state_type;
  state_type state = idle;
  
  int countc = 0;
  int count = 0;
  
  // generation of sclk
  always @ (posedge clk) begin
    if (rst == 1'b1) begin
      countc <= 0;
      sclk <= 1'b0;
    end
    else begin
      if (countc < 10)
        countc <= countc + 1;
      else begin
        countc <= 0;
        sclk <= ~sclk;
      end
    end
  end
  
  // state machine
  reg [11:0] temp;
  
  always @ (posedge sclk) begin
    if (rst == 1'b1) begin
      cs <= 1'b1;
      mosi <= 1'b0;
    end
    else begin
      case(state)
        idle: begin
          if (newd == 1'b1) begin
            state <= send;
            temp <= din;
            cs <= 1'b0;
          end
          else begin
            state <= idle;
            temp <= 8'h00;
          end
        end
        
        send: begin
          if (count < 12) begin
            mosi <= temp[count];  // sending lsb first
            count <= count + 1;
          end
          else begin
            count <= 0;
            state <= idle;
            cs <= 1'b1;
            mosi <= 1'b0;
          end
        end
        
        default: state <= idle;
      endcase
    end
  end
endmodule

/////////////////////////

module spi_slave(
  input sclk, cs, mosi,
  output [11:0] dout,
  output reg done
);
  typedef enum bit {detect_start = 1'b0, read_data = 1'b1} state_type;
  state_type state = detect_start;
  
  reg [11:0] temp = 12'h000;
  int count = 0;
  
  always @ (posedge sclk) begin
    case(state)
      detect_start: begin
        done <= 1'b0;
        if (cs == 1'b0)
          state <= read_data;
        else
          state <= detect_start;
      end
      
      read_data: begin
        if (count < 12) begin
          count <= count + 1;
          temp <= {mosi, temp[11:1]};
        end
        else begin
          count <= 0;
          done <= 1'b1;
          state <= detect_start;
        end
      end
    endcase
  end
  
  assign dout = temp;
endmodule

/////////////////////////

module top(
  input clk, rst, newd,
  input [11:0] din,
  output [11:0] dout,
  output done
);
  wire sclk, cs, mosi;
  
  spi_master m1 (clk, newd, rst, din, sclk, cs, mosi);
  spi_slave s1 (sclk, cs, mosi, dout, done);
endmodule

/////////////////////////

interface spi_if;
  logic clk, rst, newd, sclk;
  logic [11:0] din, dout;
  logic done;
endinterface
```
```
/////////////////////////

class transaction;
  bit newd;
  rand bit [11:0] din;
  bit [11:0] dout;
  
  function transaction copy();
    copy = new();
    copy.newd = this.newd;
    copy.din = this.din;
    copy.dout = this.dout;
  endfunction
endclass

/////////////////////////

class generator;
  transaction trans;
  mailbox #(transaction) mbx;
  
  int count = 0;
  
  event done;
  event drvnext;
  event sconext;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
    trans = new();
  endfunction
  
  task run();
    repeat (count) begin
      assert (trans.randomize) else $error("[GEN] : RANDOMIZATION FAILED");
      mbx.put(trans.copy);
      $display("[GEN] : din : %0d", trans.din);
      @(sconext);
    end
    -> done;
  endtask
endclass

/////////////////////////

class driver;
  virtual spi_if sif;
  transaction trans;
  mailbox #(transaction) mbx;
  mailbox #(bit [11:0]) mbxds;
  
  event drvnext;
  
  bit [11:0] din;
  
  function new(mailbox #(bit [11:0]) mbxds, mailbox #(transaction) mbx);
    this.mbx = mbx;
    this.mbxds = mbxds;
  endfunction
  
  task reset();
    sif.rst <= 1'b1;
    sif.newd <= 1'b0;
    sif.din <= 1'b0;
    repeat (10) @ (posedge sif.clk);
    sif.rst <= 1'b0;
    repeat (5) @ (posedge sif.clk);
    
    $display("[DRV] : RESET DONE");
    $display("----------------------------");
  endtask
  
  task run();
    forever begin
      mbx.get(trans);
      sif.newd <= 1'b1;
      sif.din <= trans.din;
      mbxds.put(trans.din);
      @(posedge sif.sclk);
      sif.newd <= 1'b0;
      @(posedge sif.done);
      $display("[DRV] : DATA SENT TO DAC : %0d", trans.din);
      @(posedge sif.sclk);
    end
  endtask
endclass

/////////////////////////

class monitor;
  transaction trans;
  mailbox #(bit [11:0]) mbx;
  
  virtual spi_if sif;
  
  function new(mailbox #(bit [11:0]) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
    trans = new();
    forever begin
      @(posedge sif.sclk);
      @(posedge sif.done);
      trans.dout = sif.dout;
      @(posedge sif.sclk);
      $display("[MON] : DATA SENT : %0d", trans.dout);
      mbx.put(trans.dout);
    end
  endtask
endclass

/////////////////////////

class scoreboard;
  mailbox #(bit [11:0]) mbxds, mbxms;
  bit [11:0] ds;
  bit [11:0] ms;
  
  event sconext;
  
  function new(mailbox #(bit [11:0]) mbxds, mailbox #(bit [11:0]) mbxms);
    this.mbxds = mbxds;
    this.mbxms = mbxms;
  endfunction
  
  task run();
    forever begin
      mbxds.get(ds);
      mbxms.get(ms);
      $display("[SCO] : DRV : %0d MON : %0d", ds, ms);
      
      if (ds == ms)
        $display("[SCO] : DATA MATCH");
      else
        $display("[SCO] : DATA MISMATCH");
     
      $display("----------------------------");
	  -> sconext;
    end
  endtask
endclass

/////////////////////////

class environment;
  generator gen;
  driver drv;
  monitor mon;
  scoreboard sco;
  
  event nextgd;
  event nextgs;
  
  mailbox #(transaction) mbxgd;
  mailbox #(bit [11:0]) mbxds;
  mailbox #(bit [11:0]) mbxms;
  
  virtual spi_if sif;
  
  function new(virtual spi_if sif);
  	mbxgd = new();
    mbxms = new();
    mbxds = new();

    gen = new(mbxgd);
    drv = new(mbxds,mbxgd);

    mon = new(mbxms);
    sco = new(mbxds,mbxms);

    this.sif = sif;
    drv.sif = this.sif;
    mon.sif = this.sif;

    gen.sconext = nextgs;
    sco.sconext = nextgs;
    
    gen.drvnext = nextgd;
    drv.drvnext = nextgd;
  endfunction
  
  task pre_test();
    drv.reset();
  endtask
  
  task test();
    fork
      gen.run();
      drv.run();
      mon.run();
      sco.run();
    join_any
  endtask
  
  task post_test();
    wait(gen.done.triggered);
    $finish();
  endtask
  
  task run();
    pre_test();
    test();
    post_test();
  endtask
endclass

/////////////////////////

module tb;
  spi_if sif();
  
  top dut(sif.clk,sif.rst,sif.newd,sif.din,sif.dout,sif.done);
  
  initial begin
    sif.clk <= 0;
  end
    
  always #10 sif.clk <= ~sif.clk;
  
  environment env;
  
  assign sif.sclk = dut.m1.sclk;
  
  initial begin
    env = new(sif);
    env.gen.count = 4;
    env.run();
  end
      
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
endmodule
```
```
# KERNEL: [DRV] : RESET DONE
# KERNEL: ----------------------------
# KERNEL: [GEN] : din : 935
# KERNEL: [DRV] : DATA SENT TO DAC : 935
# KERNEL: [MON] : DATA SENT : 935
# KERNEL: [SCO] : DRV : 935 MON : 935
# KERNEL: [SCO] : DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN] : din : 4060
# KERNEL: [DRV] : DATA SENT TO DAC : 4060
# KERNEL: [MON] : DATA SENT : 4060
# KERNEL: [SCO] : DRV : 4060 MON : 4060
# KERNEL: [SCO] : DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN] : din : 3576
# KERNEL: [DRV] : DATA SENT TO DAC : 3576
# KERNEL: [MON] : DATA SENT : 3576
# KERNEL: [SCO] : DRV : 3576 MON : 3576
# KERNEL: [SCO] : DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN] : din : 3153
# KERNEL: [DRV] : DATA SENT TO DAC : 3153
# KERNEL: [MON] : DATA SENT : 3153
# KERNEL: [SCO] : DRV : 3153 MON : 3153
# KERNEL: [SCO] : DATA MATCH
# KERNEL: ----------------------------
```
