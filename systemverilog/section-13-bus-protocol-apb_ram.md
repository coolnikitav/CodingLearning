# Bus Protocol: Verification of APB_RAM

Advanced Peripheral Bus Signals
- Used to communicate with peripheral components
- Single chanel

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d613b276-df7d-4fe0-81a6-d80b089cd427)

Signals
- PCLK
- PRESETn - synch. reset
- PADDR - [31:0]
- PDATA - 8, 16, 32 bits
- PWRITE - 0 = READ, 1 = WRITE
- PSTRB - [3:0] - select which of the data bits are valid. 0 = [7:0], 1 = [15:8], 2 = [23:16], 3 = [31:24]
- PSEL - select slave
- PENABLE - enable
- PRDATA - [31:0] read data from slave
- PREADY - slave indicates when data is valid
- PSLVERR - slave error
- PPROT - [2:0], protection signal, 0 = priveleged/nonpriveleged, 1 = secure/nonsecure, 2 = data/control

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/71ad7e20-ba9b-4895-a1a2-396cfc6ba6f6)

```
module apb_ram
  (
    input presetn,
    input pclk,
    input psel,
    input penable,
    input pwrite,
    input [31:0] paddr, pwdata,
    output reg [31:0] prdata,
    output reg pready, pslverr
  );
  reg [31:0] mem [32];
  
  typedef enum {idle = 0, setup = 1, access = 2, transfer = 3} state_type;
  state_type state = idle, next_state = idle;
  
  always @ (posedge pclk) begin
    if (presetn == 1'b0) begin  // active low
      state <= idle;
      prdata <= 32'h0000_0000;
      pready <= 1'b0;
      pslverr <= 1'b0;
      
      for (int i = 0; i < 32; i++) begin
        mem[i] <= 0;
      end
    end else begin
      case (state)
        idle: begin
          prdata <= 32'h0000_0000;
          pready <= 1'b0;
          pslverr <= 1'b0;
          
          if ( (psel == 1'b0) && (penable == 1'b0) ) begin
            state <= setup;
          end
        end
        setup: begin  // start of transaction
          if ( (psel == 1'b1) && (penable == 1'b0) ) begin
            if (paddr < 32) begin
              state <= access;
              pready <= 1'b1;
            end else begin
              state <= access;
              pready <= 1'b0;
            end
          end else begin
            state <= setup;
          end
        end
        access: begin
          if (psel && pwrite && penable) begin
            if (paddr< 32) begin
              mem[paddr] <= pwdata;
              state <= transfer;
              pslverr <= 1'b0;
            end else begin
              state <= transfer;
              pready <= 1'b1;
              pslverr <= 1'b1;
            end
          end else if (psel && !pwrite && penable) begin
            if (paddr < 32) begin
              prdata <= mem[paddr];
              state <= transfer;
              pready <= 1'b1;
              pslverr <= 1'b0;
            end else begin
              state <= transfer;
              pready <= 1'b1;
              pslverr <= 1'b1;
              prdata <= 32'hxxxx_xxxx;
            end
          end
        end
        transfer: begin
          state <= setup;
          pready <= 1'b0;
          pslverr <= 1'b0;
        end
        default: state <= idle;
      endcase
    end
  end
endmodule

interface apb_if;
  logic presetn;
  logic pclk;
  logic psel;
  logic penable;
  logic pwrite;
  logic [31:0] paddr, pwdata;
  logic [31:0] prdata;
  logic pready, pslverr;
endinterface
```
```
class transaction;
  typedef enum int {write = 0, read = 1, random = 2, error = 3} op_type;
  
  randc op_type oper;
  rand bit [31:0] paddr;
  rand bit [31:0] pwdata;
  rand bit psel;
  rand bit penable;
  rand bit pwrite;
  
  bit [31:0] prdata;
  bit pready;
  bit pslverr;
  
  constraint addr_c {
   paddr > 1; paddr < 5; 
  }
  
  constraint data_c {
   pwdata > 1; pwdata < 10; 
  }
  
  function void display(input string tag);
    $display("[%0s]: OP: %0s | paddr: %0d | pwdata: %0d | psel: %0b | penable: %0b | pwrite: %0b | prdata: %0d | pready: %0b | pslverr: %0b", tag,oper.name(),paddr,pwdata,psel,penable,pwrite,prdata,pready,pslverr);
  endfunction
  
  function transaction copy();
    copy = new();
    copy.oper = this.oper;
    copy.paddr = this.paddr;
    copy.pwdata = this.pwdata;
    copy.psel = this.psel;
    copy.penable = this.penable;
    copy.pwrite = this.pwrite;
    copy.prdata = this.prdata;
    copy.pready = this.pready;
    copy.pslverr = this.pslverr;
  endfunction
endclass

/////////////////////////

class generator;
  transaction tr;
  
  mailbox #(transaction) mbx;
  
  int count = 0;
  
  event drvnext;  // driver completed task of triggering interface
  event sconext;  // scoreboard completed ts objective
  event done;  
  
  function new(mailbox #(transaction) mbx);
    tr = new();
    this.mbx = mbx;    
  endfunction
  
  task run();
    repeat(count) begin
      assert(tr.randomize()) else $error("Randomization failed");
      mbx.put(tr.copy);
      tr.display("GEN");
      @(drvnext);
      @(sconext);
      $display("----------------------------");
    end
    -> done;
  endtask
endclass

/////////////////////////

class driver;
  virtual apb_if vif;
  mailbox #(transaction) mbx;
  transaction datac;
  
  event drvnext;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;    
  endfunction
  
  task reset();
    vif.presetn <= 1'b0;
    vif.psel <= 1'b0;
    vif.penable <= 1'b0;
    vif.pwdata <= 0;
    vif.paddr <= 0;
    vif.pwrite <= 1'b0;
    repeat(5) @(posedge vif.pclk);
    vif.presetn <= 1'b1;
    repeat(5) @(posedge vif.pclk);
    $display("[DRV]: RESET DONE");
  endtask
  
  task write();
    @(posedge vif.pclk);
    vif.psel <= 1'b1;
    vif.penable <= 1'b0;
    vif.pwdata <= datac.pwdata;
    vif.paddr <= datac.paddr;
    vif.pwrite <= 1'b1;
    @(posedge vif.pclk);
    vif.penable <= 1'b1;
    repeat(2) @(posedge vif.pclk);
    vif.psel <= 1'b0;
    vif.penable <= 1'b0;
    vif.pwrite <= 1'b0;
    $display("[DRV]: DATA WRITE OP data: %0d and addr: %0d",datac.pwdata,datac.paddr);
  endtask
  
  task read();
    @(posedge vif.pclk);
    vif.psel <= 1'b1;
    vif.penable <= 1'b0;
    vif.pwdata <= datac.pwdata;
    vif.paddr <= datac.paddr;
    vif.pwrite <= 1'b0;        
    @(posedge vif.pclk);
    vif.penable <= 1'b1;        
    repeat(2) @(posedge vif.pclk);
    vif.psel <= 1'b0;
    vif.penable <= 1'b0;
    vif.pwrite <= 1'b0;
    $display("[DRV]: DATA READ OP addr: %0d",datac.paddr);
  endtask
  
  task random();
    @(posedge vif.pclk);
    vif.psel <= 1'b1;
    vif.penable <= 1'b0;
    vif.pwdata <= datac.pwdata;
    vif.paddr <= datac.paddr;
    vif.pwrite <= datac.pwrite;
    @(posedge vif.pclk);
    vif.penable <= 1'b1;
    repeat(2) @(posedge vif.pclk);
    vif.psel <= 1'b0;
    vif.penable <= 1'b0;
    vif.pwrite <= 1'b0;
    $display("[DRV]: RANDOM OPERATION");
  endtask
  
  task error();
    @(posedge vif.pclk);
    vif.psel <= 1'b1;
    vif.penable <= 1'b0;
    vif.pwdata <= datac.pwdata;
    vif.paddr <= $urandom_range(32,100);
    vif.pwrite <= datac.pwrite;
    @(posedge vif.pclk);
    vif.penable <= 1;
    repeat(2) @(posedge vif.pclk);
    vif.psel <= 1'b0;
    vif.penable <= 1'b0;
    vif.pwrite <= 1'b0;
    $display("[DRV]: SLV ERROR");
  endtask
  
  task run();
    forever begin
      mbx.get(datac); 
      case (datac.oper.name())
        "write": write();
        "read": read();
        "random": random();
        "error": error();
      endcase
      -> drvnext;
    end
  endtask
  
endclass

/////////////////////////

class monitor;
  virtual apb_if vif;
  mailbox #(transaction) mbx;
  transaction tr;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
    tr = new();
    forever begin
      @(posedge vif.pclk);
      if ( (vif.psel) && (!vif.penable) ) begin
        @(posedge vif.pclk);
        if (vif.psel && vif.pwrite && vif.penable) begin
          @(posedge vif.pclk);
          tr.pwdata = vif.pwdata;
          tr.paddr = vif.paddr;
          tr.pwrite = vif.pwrite;
          tr.pslverr = vif.pslverr;
          $display("[MON]: DATA WRITE data: %0d and addr: %0d write: %0b",vif.pwdata,vif.paddr,vif.pwrite);
          @(posedge vif.pclk);
        end else if (vif.psel && !vif.pwrite && vif.penable) begin
          @(posedge vif.pclk); 
          tr.prdata = vif.prdata;
          tr.pwrite = vif.pwrite;
          tr.paddr = vif.paddr;
          tr.pslverr = vif.pslverr;
          @(posedge vif.pclk);
          $display("[MON]: DATA READ data: %0d and addr: %0d write: %0b",vif.prdata,vif.paddr,vif.pwrite);
        end
        mbx.put(tr);
      end
    end
  endtask
endclass

/////////////////////////

class scoreboard;
  mailbox #(transaction) mbx;
  transaction tr;
  
  event sconext;
  
  bit [31:0] pwdata[12] = '{default:0};
  bit [31:0] rdata;
  
  int index;
    
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
    forever begin
      mbx.get(tr);
      $display("[SCO]: DATA RCVD wdata: %0d rdata: %0d addr: %0d write: %0b",tr.pwdata,tr.prdata,tr.paddr,tr.pwrite);
      if ( (tr.pwrite == 1'b1) && (tr.pslverr == 1'b0) ) begin  // write access
        pwdata[tr.paddr] = tr.pwdata;
        $display("[SCO]: DATA STORED data: %0d addr: %0d",tr.pwdata,tr.paddr);
      end else if ( (tr.pwrite == 1'b0) && (tr.pslverr == 1'b0) ) begin  // read access
        rdata = pwdata[tr.paddr];
        if (tr.prdata == rdata)
          $display("[SCO]: DATA MATCH");
        else
          $display("[SCO]: DATA MISMATCH");
      end else if (tr.pslverr == 1'b1) begin
        $display("[SCO]: SLV ERROR DETECTED");
      end
      -> sconext;
    end    
  endtask
endclass

/////////////////////////

class environment;
  mailbox #(transaction) gdmbx;
  mailbox #(transaction) msmbx;
  
  generator gen;
  driver drv;
  monitor mon;
  scoreboard sco;
  
  event gdnext;  // drvnext
  event gsnext;  // sconext
  
  virtual apb_if vif;
    
  function new(virtual apb_if vif);
    gdmbx = new();
    msmbx = new();
    
    gen = new(gdmbx);
    drv = new(gdmbx);
    mon = new(msmbx);
    sco = new(msmbx);
    
    this.vif = vif;
    drv.vif = this.vif;
    mon.vif = this.vif;
    
    gen.drvnext = gdnext;
    drv.drvnext = gdnext;
    gen.sconext = gsnext;
    sco.sconext = gsnext;
  endfunction
  
  task pre_test();
    $display("----------------------------");
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
  apb_if vif();
  apb_ram dut(vif.presetn,vif.pclk,vif.psel,vif.penable,vif.pwrite,vif.paddr,vif.pwdata,vif.prdata,vif.pready,vif.pslverr);
  
  initial begin
    vif.pclk <= 0;
  end
  
  always #5 vif.pclk <= ~vif.pclk;
  
  environment env;
  
  initial begin
    env = new(vif);
    env.gen.count = 30;
    env.run();
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
endmodule
```
```
# KERNEL: ----------------------------
# KERNEL: [DRV]: RESET DONE
# KERNEL: [GEN]: OP: write | paddr: 3 | pwdata: 3 | psel: 1 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: DATA WRITE OP data: 3 and addr: 3
# KERNEL: [MON]: DATA WRITE data: 3 and addr: 3 write: 1
# KERNEL: [SCO]: DATA RCVD wdata: 3 rdata: 0 addr: 3 write: 1
# KERNEL: [SCO]: DATA STORED data: 3 addr: 3
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: read | paddr: 2 | pwdata: 9 | psel: 0 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: DATA READ OP addr: 2
# KERNEL: [MON]: DATA READ data: 0 and addr: 2 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 3 rdata: 0 addr: 2 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: random | paddr: 4 | pwdata: 7 | psel: 0 | penable: 0 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 7 and addr: 4 write: 1
# KERNEL: [DRV]: RANDOM OPERATION
# KERNEL: [SCO]: DATA RCVD wdata: 7 rdata: 0 addr: 4 write: 1
# KERNEL: [SCO]: DATA STORED data: 7 addr: 4
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: error | paddr: 3 | pwdata: 3 | psel: 1 | penable: 0 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 3 and addr: 71 write: 1
# KERNEL: [DRV]: SLV ERROR
# KERNEL: [SCO]: DATA RCVD wdata: 3 rdata: 0 addr: 71 write: 1
# KERNEL: [SCO]: SLV ERROR DETECTED
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: write | paddr: 3 | pwdata: 9 | psel: 1 | penable: 1 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 9 and addr: 3 write: 1
# KERNEL: [DRV]: DATA WRITE OP data: 9 and addr: 3
# KERNEL: [SCO]: DATA RCVD wdata: 9 rdata: 0 addr: 3 write: 1
# KERNEL: [SCO]: DATA STORED data: 9 addr: 3
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: read | paddr: 3 | pwdata: 5 | psel: 1 | penable: 0 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: DATA READ OP addr: 3
# KERNEL: [MON]: DATA READ data: 9 and addr: 3 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 9 rdata: 9 addr: 3 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: random | paddr: 3 | pwdata: 4 | psel: 0 | penable: 1 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: RANDOM OPERATION
# KERNEL: [MON]: DATA READ data: 9 and addr: 3 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 9 rdata: 9 addr: 3 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: error | paddr: 3 | pwdata: 8 | psel: 0 | penable: 1 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 8 and addr: 54 write: 1
# KERNEL: [DRV]: SLV ERROR
# KERNEL: [SCO]: DATA RCVD wdata: 8 rdata: 9 addr: 54 write: 1
# KERNEL: [SCO]: SLV ERROR DETECTED
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: write | paddr: 2 | pwdata: 4 | psel: 1 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 4 and addr: 2 write: 1
# KERNEL: [DRV]: DATA WRITE OP data: 4 and addr: 2
# KERNEL: [SCO]: DATA RCVD wdata: 4 rdata: 9 addr: 2 write: 1
# KERNEL: [SCO]: DATA STORED data: 4 addr: 2
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: random | paddr: 2 | pwdata: 6 | psel: 1 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: RANDOM OPERATION
# KERNEL: [MON]: DATA READ data: 4 and addr: 2 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 4 rdata: 4 addr: 2 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: read | paddr: 3 | pwdata: 8 | psel: 0 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: DATA READ OP addr: 3
# KERNEL: [MON]: DATA READ data: 9 and addr: 3 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 4 rdata: 9 addr: 3 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: error | paddr: 3 | pwdata: 9 | psel: 0 | penable: 1 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: SLV ERROR
# KERNEL: [MON]: DATA READ data: x and addr: 37 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 4 rdata: 0 addr: 37 write: 0
# KERNEL: [SCO]: SLV ERROR DETECTED
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: random | paddr: 2 | pwdata: 5 | psel: 0 | penable: 1 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 5 and addr: 2 write: 1
# KERNEL: [DRV]: RANDOM OPERATION
# KERNEL: [SCO]: DATA RCVD wdata: 5 rdata: 0 addr: 2 write: 1
# KERNEL: [SCO]: DATA STORED data: 5 addr: 2
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: write | paddr: 2 | pwdata: 3 | psel: 0 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 3 and addr: 2 write: 1
# KERNEL: [DRV]: DATA WRITE OP data: 3 and addr: 2
# KERNEL: [SCO]: DATA RCVD wdata: 3 rdata: 0 addr: 2 write: 1
# KERNEL: [SCO]: DATA STORED data: 3 addr: 2
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: error | paddr: 3 | pwdata: 9 | psel: 1 | penable: 1 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 9 and addr: 50 write: 1
# KERNEL: [DRV]: SLV ERROR
# KERNEL: [SCO]: DATA RCVD wdata: 9 rdata: 0 addr: 50 write: 1
# KERNEL: [SCO]: SLV ERROR DETECTED
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: read | paddr: 3 | pwdata: 8 | psel: 0 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: DATA READ OP addr: 3
# KERNEL: [MON]: DATA READ data: 9 and addr: 3 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 9 rdata: 9 addr: 3 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: error | paddr: 4 | pwdata: 4 | psel: 0 | penable: 0 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 4 and addr: 47 write: 1
# KERNEL: [DRV]: SLV ERROR
# KERNEL: [SCO]: DATA RCVD wdata: 4 rdata: 9 addr: 47 write: 1
# KERNEL: [SCO]: SLV ERROR DETECTED
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: write | paddr: 3 | pwdata: 5 | psel: 1 | penable: 0 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 5 and addr: 3 write: 1
# KERNEL: [DRV]: DATA WRITE OP data: 5 and addr: 3
# KERNEL: [SCO]: DATA RCVD wdata: 5 rdata: 9 addr: 3 write: 1
# KERNEL: [SCO]: DATA STORED data: 5 addr: 3
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: read | paddr: 3 | pwdata: 9 | psel: 1 | penable: 1 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: DATA READ OP addr: 3
# KERNEL: [MON]: DATA READ data: 5 and addr: 3 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 5 rdata: 5 addr: 3 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: random | paddr: 4 | pwdata: 9 | psel: 0 | penable: 0 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 9 and addr: 4 write: 1
# KERNEL: [DRV]: RANDOM OPERATION
# KERNEL: [SCO]: DATA RCVD wdata: 9 rdata: 5 addr: 4 write: 1
# KERNEL: [SCO]: DATA STORED data: 9 addr: 4
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: read | paddr: 4 | pwdata: 9 | psel: 0 | penable: 0 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: DATA READ OP addr: 4
# KERNEL: [MON]: DATA READ data: 9 and addr: 4 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 9 rdata: 9 addr: 4 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: error | paddr: 4 | pwdata: 7 | psel: 1 | penable: 1 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 7 and addr: 81 write: 1
# KERNEL: [DRV]: SLV ERROR
# KERNEL: [SCO]: DATA RCVD wdata: 7 rdata: 9 addr: 81 write: 1
# KERNEL: [SCO]: SLV ERROR DETECTED
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: write | paddr: 4 | pwdata: 5 | psel: 1 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 5 and addr: 4 write: 1
# KERNEL: [DRV]: DATA WRITE OP data: 5 and addr: 4
# KERNEL: [SCO]: DATA RCVD wdata: 5 rdata: 9 addr: 4 write: 1
# KERNEL: [SCO]: DATA STORED data: 5 addr: 4
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: random | paddr: 4 | pwdata: 7 | psel: 0 | penable: 0 | pwrite: 1 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 7 and addr: 4 write: 1
# KERNEL: [DRV]: RANDOM OPERATION
# KERNEL: [SCO]: DATA RCVD wdata: 7 rdata: 9 addr: 4 write: 1
# KERNEL: [SCO]: DATA STORED data: 7 addr: 4
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: random | paddr: 4 | pwdata: 8 | psel: 0 | penable: 1 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: RANDOM OPERATION
# KERNEL: [MON]: DATA READ data: 7 and addr: 4 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 7 rdata: 7 addr: 4 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: write | paddr: 4 | pwdata: 2 | psel: 1 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 2 and addr: 4 write: 1
# KERNEL: [DRV]: DATA WRITE OP data: 2 and addr: 4
# KERNEL: [SCO]: DATA RCVD wdata: 2 rdata: 7 addr: 4 write: 1
# KERNEL: [SCO]: DATA STORED data: 2 addr: 4
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: read | paddr: 4 | pwdata: 8 | psel: 0 | penable: 1 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: DATA READ OP addr: 4
# KERNEL: [MON]: DATA READ data: 2 and addr: 4 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 2 rdata: 2 addr: 4 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: error | paddr: 4 | pwdata: 4 | psel: 1 | penable: 1 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: SLV ERROR
# KERNEL: [MON]: DATA READ data: x and addr: 39 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 2 rdata: 0 addr: 39 write: 0
# KERNEL: [SCO]: SLV ERROR DETECTED
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: read | paddr: 4 | pwdata: 7 | psel: 1 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [DRV]: DATA READ OP addr: 4
# KERNEL: [MON]: DATA READ data: 2 and addr: 4 write: 0
# KERNEL: [SCO]: DATA RCVD wdata: 2 rdata: 2 addr: 4 write: 0
# KERNEL: [SCO]: DATA MATCH
# KERNEL: ----------------------------
# KERNEL: [GEN]: OP: write | paddr: 2 | pwdata: 6 | psel: 1 | penable: 0 | pwrite: 0 | prdata: 0 | pready: 0 | pslverr: 0
# KERNEL: [MON]: DATA WRITE data: 6 and addr: 2 write: 1
# KERNEL: [DRV]: DATA WRITE OP data: 6 and addr: 2
# KERNEL: [SCO]: DATA RCVD wdata: 6 rdata: 2 addr: 2 write: 1
# KERNEL: [SCO]: DATA STORED data: 6 addr: 2
# KERNEL: ----------------------------
```
