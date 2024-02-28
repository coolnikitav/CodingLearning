# Communication protocol: verification of UART
```
module uarttx
  #( 
    parameter clk_freq = 1_000_000,
    parameter baud_rate = 9600
  )
  (
    input clk, rst,
    input newd,
    input [7:0] tx_data,
    output reg tx,
    output reg donetx
  );
  localparam clkcount = (clk_freq/baud_rate);
  
  integer count = 0;
  integer counts = 0;
  
  reg uclk = 0;
  
  enum bit[1:0] {idle = 2'b00, start = 2'b01, transfer = 2'b10, done = 2'b11} state;
  
  // uart_clock_gen
  always @ (posedge clk) begin
    if (count < clkcount / 2)
      count <= count + 1;
    else begin
      count <= 0;
      uclk <= ~uclk;
    end
  end
  
  reg [7:0] din;
  
  // state transition
  always @ (posedge uclk) begin
    if (rst) begin
      state <= idle;
    end 
    else begin
      case(state)
        idle: begin
          counts <= 0;
          tx <= 1'b1;
          donetx <= 1'b0;
          
          if (newd) begin
            state <= transfer;
            din <= tx_data;
            tx <= 1'b0;
          end 
          else begin
            state <= idle;
          end
        end
        
        transfer: begin
          if (counts <= 7) begin
            counts <= counts + 1;
            tx <= din[counts];
            state <= transfer;
          end
          else begin
            counts <= 0;
            tx <= 1'b1;
            state <= idle;
            donetx <= 1'b1;
          end
        end
        
        default: state <= idle;
      endcase
    end
  end
endmodule

////////////////////////////////

module uartrx
  #( 
    parameter clk_freq = 1_000_000,
    parameter baud_rate = 9600
  )
  (
    input clk, rst,
    input rx,
    output reg done,
    output reg [7:0] rxdata
  );
  localparam clkcount = (clk_freq/baud_rate);
  
  integer count = 0;
  integer counts = 0;
  
  reg uclk = 0;
  
  enum bit[1:0] {idle = 2'b00, start = 2'b01} state;
  
  // uart_clock_gen
  always @ (posedge clk) begin
    if (count < clkcount / 2)
      count <= count + 1;
    else begin
      count <= 0;
      uclk <= ~uclk;
    end
  end
  
  // state transition
  always @ (posedge uclk) begin
    if (rst) begin
      rxdata <= 8'h00;
      counts <= 0;
      done <= 1'b0;
    end
    else begin
      case (state)
        idle: begin
          rxdata <= 8'h00;
          counts <= 0;
          done <= 1'b0;
          
          if (rx == 1'b0)
            state <= start;
          else
            state <= idle;
        end
        
        start: begin
          if (counts < 8) begin
            counts <= counts + 1;
            rxdata <= {rx, rxdata[7:1]};
          end
          else begin
            counts <= 0;
            done <= 1'b1;
            state <= idle;
          end
        end
        
        default: state <= idle;
      endcase
    end
  end
endmodule

////////////////////////////////

module uart_top
  #( 
    parameter clk_freq = 1_000_000,
    parameter baud_rate = 9600
  )
  (
    input clk,rst,
    input rx,
    input [7:0] dintx,
    input newd,
    output tx,
    output [7:0] doutrx,
    output donetx,
    output donerx
  );
  
  uarttx #(clk_freq, baud_rate) utx (clk, rst, newd, dintx, tx, donetx);
  uartrx #(clk_freq, baud_rate) rtx (clk, rst, rx, donerx, doutrx);
endmodule

////////////////////////////////

interface uart_if;
  logic clk,rst;
  logic uclktx,uclkrx;
  logic rx;
  logic [7:0] dintx;
  logic newd;
  logic tx;
  logic [7:0] doutrx;
  logic donetx;
  logic donerx;
endinterface
```
```
class transaction;
  typedef enum bit {write = 1'b0, read = 1'b1} oper_type;
  randc oper_type oper;
  rand bit [7:0] dintx;
  
  bit rx;
  bit newd;
  bit tx;
  bit [7:0] doutrx;
  bit donetx;
  bit donerx;
  
  function transaction copy();
    copy = new();
    copy.rx = this.rx;
    copy.dintx = this.dintx;
    copy.newd = this.newd;
    copy.tx = this.tx;
    copy.doutrx = this.doutrx;
    copy.donetx = this.donetx;
    copy.donerx = this.donerx;
    copy.oper = this.oper;
  endfunction
endclass

////////////////////////////////

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
      assert(trans.randomize) else $error("[GEN] : RANDOMIZATION FAILED");
      mbx.put(trans.copy);
      $display("[GEN] : oper : %0s  din : %0d", trans.oper.name(), trans.dintx);
      @(drvnext);
      @(sconext);
    end
    -> done;
  endtask
endclass

////////////////////////////////

class driver;
  virtual uart_if uif;
  transaction trans;
  mailbox #(transaction) mbx;
  mailbox #(bit [7:0]) mbxds;
  
  event drvnext;
  
  bit [7:0] din;
  bit wr = 0;  // random operation read/write
  bit [7:0] datarx;  // data rcvd during read
  
  function new(mailbox #(bit [7:0]) mbxds, mailbox #(transaction) mbx);
    this.mbx = mbx;
    this.mbxds = mbxds;
  endfunction
  
  task reset();
    uif.rst <= 1'b1;
    uif.dintx <= 0;
    uif.newd <= 0;
    uif.rx <= 1'b1;
    
    repeat(5) @(posedge uif.uclktx);
    uif.rst <= 1'b0;
    @(posedge uif.uclktx);
    $display("[DRV] : RESET DONE");
    $display("--------------------------------");
  endtask
    
  task run();
    forever begin
      mbx.get(trans);
      
      if(trans.oper == 1'b0) begin  // data transmission -> write
        @(posedge uif.uclktx);
        uif.rst <= 1'b0;
        uif.newd <= 1'b1;  // start data sending op
        uif.rx <= 1'b1;
        uif.dintx <= trans.dintx;
        @(posedge uif.uclktx);
        uif.newd <= 1'b0;
        mbxds.put(trans.dintx);
        $display("[DRV] : DATA SENT : %0d", trans.dintx);
        wait (uif.donetx == 1'b1);
        -> drvnext;
      end
      else if (trans.oper == 1'b1) begin
        @(posedge uif.uclkrx);
        uif.rst <= 1'b0;
        uif.rx <= 1'b0;
        uif.newd <= 1'b0;
        @(posedge uif.uclkrx);
        
        for (int i = 0; i < 8; i++) begin
          @(posedge uif.uclkrx);
          uif.rx <= $urandom;
          datarx[i] = uif.rx;
        end
        
        mbxds.put(datarx);
        $display("[DRV] : DATA RCVD : %0d", datarx);
        wait (uif.donerx == 1'b1);
        uif.rx <= 1'b1;
        -> drvnext;
      end
    end
  endtask
endclass

////////////////////////////////

class monitor;
 
  transaction tr;
  
  mailbox #(bit [7:0]) mbx;
  
  bit [7:0] srx; //////send
  bit [7:0] rrx; ///// recv
  
 
  
  virtual uart_if uif;
  
  
  function new(mailbox #(bit [7:0]) mbx);
    this.mbx = mbx;
    endfunction
  
  task run();
    
    forever begin
     
      @(posedge uif.uclktx);
      if ( (uif.newd== 1'b1) && (uif.rx == 1'b1) ) 
                begin
                  
                  @(posedge uif.uclktx); ////start collecting tx data from next clock tick
                  
              for(int i = 0; i<= 7; i++) 
              begin 
                @(posedge uif.uclktx);
                srx[i] = uif.tx;
                    
              end
 
                  
                  $display("[MON] : DATA SEND on UART TX %0d", srx);
                  
                  //////////wait for done tx before proceeding next transaction                
                  @(posedge uif.uclktx); //
                mbx.put(srx);
                 
               end
      
      else if ((uif.rx == 1'b0) && (uif.newd == 1'b0) ) 
        begin
          wait(uif.donerx == 1);
           rrx = uif.doutrx;     
           $display("[MON] : DATA RCVD RX %0d", rrx);
          @(posedge uif.uclktx); 
           mbx.put(rrx);
      end
  end  
endtask

endclass

////////////////////////////////

class scoreboard;
  mailbox #(bit [7:0]) mbxds, mbxms;
  
  bit [7:0] ds;
  bit [7:0] ms;
  
   event sconext;
  
  function new(mailbox #(bit [7:0]) mbxds, mailbox #(bit [7:0]) mbxms);
    this.mbxds = mbxds;
    this.mbxms = mbxms;
  endfunction
  
  task run();
    forever begin
      
      mbxds.get(ds);
      mbxms.get(ms);
      
      $display("[SCO] : DRV : %0d MON : %0d", ds, ms);
      if(ds == ms)
        $display("DATA MATCHED");
      else
        $display("DATA MISMATCHED");
      
      $display("----------------------------------------");
      
     ->sconext; 
    end
  endtask
  
  
endclass

////////////////////////////////

class environment;
 
    generator gen;
    driver drv;
    monitor mon;
    scoreboard sco; 
  
    event nextgd; ///gen -> drv
  
    event nextgs;  /// gen -> sco
  
  mailbox #(transaction) mbxgd; ///gen - drv
  
  mailbox #(bit [7:0]) mbxds; /// drv - sco
    
     
  mailbox #(bit [7:0]) mbxms;  /// mon - sco
  
    virtual uart_if uif;
 
  
  function new(virtual uart_if uif);
       
    mbxgd = new();
    mbxms = new();
    mbxds = new();
    
    gen = new(mbxgd);
    drv = new(mbxds,mbxgd);
    
    
 
    mon = new(mbxms);
    sco = new(mbxds, mbxms);
    
    this.uif = uif;
    drv.uif = this.uif;
    mon.uif = this.uif;
    
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

////////////////////////////////

module tb;
  generator gen;
  driver drv;
  monitor mon;
  
  event sconext;
  event drvnext;
  
  event done;
  
  mailbox #(transaction) mbx;
  mailbox #(bit [7:0]) mbxds;
  mailbox #(bit [7:0]) mbxms;
  
  uart_if uif();
  
  uart_top #(1000000, 9600) dut (uif.clk,uif.rst,uif.rx,uif.dintx,uif.newd,uif.tx,uif.doutrx,uif.donetx, uif.donerx);
  
  
  
    initial begin
      uif.clk <= 0;
    end
    
    always #10 uif.clk <= ~uif.clk;
  
  
  environment env;
  
  initial begin
    env = new(uif);
    env.gen.count = 5;
    env.run();
  end
 
  
  initial begin
  $dumpfile("dump.vcd");
    $dumpvars;
  end
  
  
     
assign uif.uclktx = dut.utx.uclk;
assign uif.uclkrx = dut.rtx.uclk;
    
  
  
endmodule
```
