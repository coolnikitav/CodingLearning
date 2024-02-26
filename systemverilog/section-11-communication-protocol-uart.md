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
    input newd,
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
        $display("[DRV] : DATA RCVD : %0d", trans.datarx);
        wait (uif.donerx == 1'b1);
        uif.rx <= 1'b1;
        -> drvnext;
      end
    end
  endtask
endclass
```
