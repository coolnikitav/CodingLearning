# Verification environment for first in first out (FIFO)
```
module FIFO(input clk, rst, wr,rd,
            input [7:0] din, output reg [7:0] dout,
            output empty, full);
  
  reg [3:0] wptr = 0, rptr = 0;
  reg [4:0] cnt = 0;
  reg [7:0] mem [15:0];
  
  always @ (posedge clk)
    begin
      if (rst == 1'b1)
        begin
          wptr <= 0;
          rptr <= 0;
          cnt <= 0;
        end
      else if (wr && !full)
        begin
          mem[wptr] <= din;
          wptr <= wptr + 1;
          cnt <= cnt + 1;
        end
      else if (rd && !empty)
        begin
          dout <= mem[rptr];
          rptr <= rptr + 1;
          cnt <= cnt - 1;
        end
    end
  
  assign empty = (cnt == 0) ? 1'b1 : 1'b0;
  assign full = (cnt == 16) ? 1'b1 : 1'b0;
  
endmodule

interface fifo_if; 
  logic clk, rd, wr;
  logic full, empty;
  logic [7:0] din, dout;
  logic rst;
endinterface
```
```
/////////////////////////////////

class transaction;
  
  rand bit op;
  bit rd, wr;
  bit [7:0] din, dout;
  bit empty, full;
  
  constraint op_ctrl {
    op dist {1 := 50, 0 := 50}; 
  }
  
endclass

/////////////////////////////////

class generator;
  
  transaction trans;
  mailbox #(transaction) mbx;  // send to drv
  
  int count = 0;
  int i = 0;
  
  event next;
  event done;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
    trans = new();
  endfunction
  
  task run();
    repeat(count) begin
      assert(trans.randomize) else $error("Randomization failed");
      i++;
      mbx.put(trans);
      $display("[GEN] : OP : %0d iteration : %0d", trans.op, i);
      @(next);
    end   
    -> done;
  endtask
  
endclass

/////////////////////////////////

class driver;
  
  virtual fifo_if fif;
  mailbox #(transaction) mbx;  // receive from gen
  transaction trans;
  
  event next;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task reset();
  	fif.rst <= 1'b1;
    fif.rd <= 1'b0;
    fif.wr <= 1'b0;
    fif.din <= 0;
    repeat(5) @(posedge fif.clk);
    fif.rst <= 1'b0;
    $display("[DRV] : RESET DONE");
    $display("----------------------------");
  endtask
  
  task write();
    @(posedge fif.clk);
    fif.rst <= 1'b0;
    fif.rd <= 1'b0;
    fif.wr <= 1'b1;
    fif.din <= $urandom_range(1,10);
    @(posedge fif.clk);
    fif.wr <= 1'b0;
    $display("[DRV] : DATA WRITE data : %0d", fif.din);
    @(posedge fif.clk);
  endtask
  
  task read();
    @(posedge fif.clk);
    fif.rst <= 1'b0;
    fif.rd <= 1'b1;
    fif.wr <= 1'b0;
    @(posedge fif.clk);
    fif.rd <= 1'b0;
    $display("[DRV] : DATA READ");
    @(posedge fif.clk);
  endtask
  
  // Applying random stimulus to DUT
  task run();
    forever begin
      mbx.get(trans);
      if (trans.op == 1'b1)
        write();
      else
        read();
    end
  endtask
  
endclass

/////////////////////////////////

class monitor;
  transaction trans;
  virtual fifo_if fif;
  mailbox #(transaction) mbx;  // send to sco
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
    trans = new();
    forever begin
      repeat(2) @(posedge fif.clk);
      trans.rd = fif.rd;
      trans.wr = fif.wr;
      trans.din = fif.din;
      trans.full = fif.full;
      trans.empty = fif.empty;
      @(posedge fif.clk);
      trans.dout = fif.dout;
      
      mbx.put(trans);
      $display("[MON] : wr: %0d rd: %0d din: %0d dout: %0d full:%0d empty: %0d",trans.wr,trans.rd,trans.din,trans.dout,trans.full,trans.empty);
    end
  endtask
endclass

/////////////////////////////////

class scoreboard;
  transaction trans;
  mailbox #(transaction) mbx;
  
  event next;
  
  // golden data
  bit [7:0] din[$];
  bit [7:0] temp;
  int err = 0;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
    forever begin
      mbx.get(trans);
      $display("[SCO] : wr: %0d rd: %0d din: %0d dout: %0d full:%0d empty: %0d",trans.wr,trans.rd,trans.din,trans.dout,trans.full,trans.empty);
      if (trans.wr == 1'b1)
        begin
          if (trans.full == 1'b0)
            begin
              din.push_front(trans.din);
              $display("[SCO] : DATA STORED IN QUEUE : %0d", trans.din);
            end
          else
            begin
              $display("[SCO] : FIFO is full");
            end
          $display("----------------------------");
        end
     
      if (trans.rd == 1'b1)
        begin
          if (trans.empty == 1'b0)
            begin
              temp = din.pop_back();
              if (trans.dout == temp)
                $display("DATA MATCH");
              else begin
                $error("DATA MISMATCH");
                err++;
              end              
            end
          else 
            begin
              $display("[SCO] : FIFO is empty");
            end
          $display("----------------------------");
        end
      
      ->next;

    end
  endtask
endclass

/////////////////////////////////

class environment;
  generator gen;
  driver drv;
  monitor mon;
  scoreboard sco;
  
  mailbox #(transaction) gdmbx;
  mailbox #(transaction) msmbx;
  virtual fifo_if fif;
  
  event nextgs;
  
  function new(virtual fifo_if fif);
    gdmbx = new();
    msmbx = new();
    
    gen = new(gdmbx);
    drv = new(gdmbx);
    mon = new(msmbx);
    sco = new(msmbx);
    
    this.fif = fif;
    drv.fif = fif;
    mon.fif = fif;
    
    gen.next = nextgs;
    sco.next = nextgs;
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
    $display("----------------------------");
    $display("Error count : %0d", sco.err);
    $display("----------------------------");
    $finish;
  endtask
  
  task run();
    pre_test();
    test();
    post_test();
  endtask
endclass

/////////////////////////////////

module tb;
  
  fifo_if fif();
  FIFO dut(.clk(fif.clk),.rst(fif.rst),.wr(fif.wr),.rd(fif.rd),.din(fif.din),.dout(fif.dout),.empty(fif.empty),.full(fif.full));
  
  initial begin
    fif.clk <= 0;
  end
  
  always #10 fif.clk <= ~fif.clk;
  
  environment env;
    
  initial begin
    env = new(fif);
    env.gen.count = 10;
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
# KERNEL: [GEN] : OP : 1 iteration : 1
# KERNEL: [DRV] : DATA WRITE data : 2
# KERNEL: [MON] : wr: 1 rd: 0 din: 2 dout: 0 full:0 empty: 1
# KERNEL: [SCO] : wr: 1 rd: 0 din: 2 dout: 0 full:0 empty: 1
# KERNEL: [SCO] : DATA STORED IN QUEUE : 2
# KERNEL: ----------------------------
# KERNEL: [GEN] : OP : 1 iteration : 2
# KERNEL: [DRV] : DATA WRITE data : 7
# KERNEL: [MON] : wr: 1 rd: 0 din: 7 dout: 0 full:0 empty: 0
# KERNEL: [SCO] : wr: 1 rd: 0 din: 7 dout: 0 full:0 empty: 0
# KERNEL: [SCO] : DATA STORED IN QUEUE : 7
# KERNEL: ----------------------------
# KERNEL: [GEN] : OP : 1 iteration : 3
# KERNEL: [DRV] : DATA WRITE data : 9
# KERNEL: [MON] : wr: 1 rd: 0 din: 9 dout: 0 full:0 empty: 0
# KERNEL: [SCO] : wr: 1 rd: 0 din: 9 dout: 0 full:0 empty: 0
# KERNEL: [SCO] : DATA STORED IN QUEUE : 9
# KERNEL: ----------------------------
# KERNEL: [GEN] : OP : 1 iteration : 4
# KERNEL: [DRV] : DATA WRITE data : 7
# KERNEL: [MON] : wr: 1 rd: 0 din: 7 dout: 0 full:0 empty: 0
# KERNEL: [SCO] : wr: 1 rd: 0 din: 7 dout: 0 full:0 empty: 0
# KERNEL: [SCO] : DATA STORED IN QUEUE : 7
# KERNEL: ----------------------------
# KERNEL: [GEN] : OP : 1 iteration : 5
# KERNEL: [DRV] : DATA WRITE data : 2
# KERNEL: [MON] : wr: 1 rd: 0 din: 2 dout: 0 full:0 empty: 0
# KERNEL: [SCO] : wr: 1 rd: 0 din: 2 dout: 0 full:0 empty: 0
# KERNEL: [SCO] : DATA STORED IN QUEUE : 2
# KERNEL: ----------------------------
# KERNEL: [GEN] : OP : 0 iteration : 6
# KERNEL: [DRV] : DATA READ
# KERNEL: [MON] : wr: 0 rd: 1 din: 2 dout: 2 full:0 empty: 0
# KERNEL: [SCO] : wr: 0 rd: 1 din: 2 dout: 2 full:0 empty: 0
# KERNEL: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN] : OP : 0 iteration : 7
# KERNEL: [DRV] : DATA READ
# KERNEL: [MON] : wr: 0 rd: 1 din: 2 dout: 7 full:0 empty: 0
# KERNEL: [SCO] : wr: 0 rd: 1 din: 2 dout: 7 full:0 empty: 0
# KERNEL: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN] : OP : 0 iteration : 8
# KERNEL: [DRV] : DATA READ
# KERNEL: [MON] : wr: 0 rd: 1 din: 2 dout: 9 full:0 empty: 0
# KERNEL: [SCO] : wr: 0 rd: 1 din: 2 dout: 9 full:0 empty: 0
# KERNEL: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN] : OP : 1 iteration : 9
# KERNEL: [DRV] : DATA WRITE data : 10
# KERNEL: [MON] : wr: 1 rd: 0 din: 10 dout: 9 full:0 empty: 0
# KERNEL: [SCO] : wr: 1 rd: 0 din: 10 dout: 9 full:0 empty: 0
# KERNEL: [SCO] : DATA STORED IN QUEUE : 10
# KERNEL: ----------------------------
# KERNEL: [GEN] : OP : 0 iteration : 10
# KERNEL: [DRV] : DATA READ
# KERNEL: [MON] : wr: 0 rd: 1 din: 10 dout: 7 full:0 empty: 0
# KERNEL: [SCO] : wr: 0 rd: 1 din: 10 dout: 7 full:0 empty: 0
# KERNEL: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: Error count : 0
# KERNEL: ----------------------------
```
