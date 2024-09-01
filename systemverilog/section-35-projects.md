# Projects

## Assertions in FSM
![image](https://github.com/user-attachments/assets/7b0080cf-d60b-40d8-a446-d3e0f0c3d61b)

```
module tb;
  reg clk = 0;
  reg  din = 0;
  reg rst = 0;
  wire dout;
  
  top dut (clk,rst,din,dout);
  
  always #5 clk = ~clk;
  
  initial begin
    #3;
    rst = 1;
    #30;
    rst = 0;
    din = 1;
    #45;
    din = 0;
    #25;
    rst = 1;
    #40;
    rst = 0;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #180;
    $finish;    
  end

  ////////// (1) State is one hot encoded
  
  state_encoding : assert property (@(posedge clk) 1'b1 |-> $onehot(dut.state));

  ////////////// (2) Behavior on rst high
  
    state_rst_high:  assert property (@(posedge clk) rst |=> (dut.state == dut.idle));
  
  state_thr_rst_high:   assert property (@(posedge clk) $rose(rst) |=> (((dut.state == dut.idle)[*1:18]) within (rst[*1:18] ##1 !rst)));
 
/////////////////    (3) Behavior on rst low 
     
  sequence s1;
    (dut.next_state == dut.idle) ##1 (dut.next_state == dut.s0);    
  endsequence
 
   sequence s2;
     (dut.next_state == dut.s0) ##1 (dut.next_state == dut.s1);    
  endsequence
      
      
  sequence s3;
    (dut.next_state == dut.s1) ##1 (dut.next_state == dut.s0);    
  endsequence
      
    state_din_high: assert property (@(posedge clk) disable iff(rst) din |-> (s1 or s2 or s3));  
      
//////////////////////////////////////////////////////////////////////////////////////////////////      
   sequence s4;
     (dut.next_state == dut.idle) ##1 (dut.next_state == dut.s0);    
  endsequence
 
   sequence s5;
     (dut.next_state == dut.s0) ##1 (dut.next_state == dut.s0);    
  endsequence
      
      
  sequence s6;
    (dut.next_state == dut.s1) ##1 (dut.next_state == dut.s1);    
  endsequence 
  
      state_din_low: assert property (@(posedge clk) disable iff(rst) !din |-> (s4 or s5 or s6));    
   //////////////////////////////////////////////////////////////////////////////////////////////
 property p1;
   @(posedge clk)
   if(din)
     (s1 or s2 or s3)
   else
     (s4 or s5 or s6);
 endproperty
    
      state_din: assert property (disable iff(rst) p1);
      
  /////////////////////////////////////////////////////////// 
  ///////////////   (4) all states are cover
 
  initial assert property (@(posedge clk) (dut.state == dut.idle)[->1] |-> ##[1:18] (dut.state == dut.s0) ##[1:18] (dut.state == dut.s1)); 
    ////////////   (5)  Output check
  
    assert property (@(posedge clk) disable iff(rst) ((dut.next_state == dut.s0) && ($past(dut.next_state) == dut.s1)) |-> (dout == 1'b1) );  
endmodule
```

## Understanding bind
```
module adder
(
  input [3:0] a,b,
  output [4:0] y
);  

	assign y =  a + b;
  
endmodule

module adder_assert(
  input [3:0] a,b,
  input [4:0] y
);
  A1: assert #0 (y == a+b) $info("Suc at %0t", $time);
endmodule

module tb;
  reg [3:0] a = 0,b = 0;
  wire [4:0] y;
  
  adder dut (a,b,y);
  
  bind adder adder_assert dut(a,b,y);

  initial begin
    for(int i =0; i < 15; i++)
      begin
        a = $urandom();
        b = $urandom();
        #20;
      end
  end
  
  initial begin
   $dumpfile("dump.vcd");
   $dumpvars;
   $assertvacuousoff(0);
   #350;
   $finish;
 end
endmodule

# KERNEL: Info: testbench.sv (5): Suc at 0
# KERNEL: Info: testbench.sv (5): Suc at 40
# KERNEL: Info: testbench.sv (5): Suc at 60
# KERNEL: Info: testbench.sv (5): Suc at 80
# KERNEL: Info: testbench.sv (5): Suc at 100
# KERNEL: Info: testbench.sv (5): Suc at 120
# KERNEL: Info: testbench.sv (5): Suc at 140
# KERNEL: Info: testbench.sv (5): Suc at 160
# KERNEL: Info: testbench.sv (5): Suc at 180
# KERNEL: Info: testbench.sv (5): Suc at 200
# KERNEL: Info: testbench.sv (5): Suc at 220
# KERNEL: Info: testbench.sv (5): Suc at 240
# KERNEL: Info: testbench.sv (5): Suc at 260
# KERNEL: Info: testbench.sv (5): Suc at 280
```

## Assertions in Counter
```
module counter_assert(
  input clk,
  input rst,
  input up,
  input [3:0] dout
);
  /* (1) Behavior of the dout when rst asserted */
  ////dout is zero in next clock tick after rst
  DOUT_RST_ASRT_1: assert property (@(posedge clk) $rose(rst) |=> (dout == 0));
  
  ///// dout is zero for all clock ticks during rst
  DOUT_RST_ASRT_2: assert property (@(posedge clk) rst |-> (dout == 0));
    
  ////// dout remain stable to zero for entire duration of rst 
  DOUT_RST_ASRT_3: assert property (@(posedge clk) $rose(rst) |=> rst throughout ((dout == 0)[*1:36]));
  
    
  /* (2) dout is unknown anywhere in the simulation */   
  //////dout must be valid after rst deassert
  DOUT_UNKNW_1: assert property(@(posedge clk) $fell(rst) |-> !$isunknown(dout));
    
  ////// dout must be valid for all clock edges
  always@(posedge clk)
    begin
     DOUT_UNKNW_2: assert(!$isunknown(dout));
    end

    
  /* (3)   verifying up and down state of the counter  */  
  //////current value of dout must be one greater than previous value when up = 1     
  UP_MODE_1: assert property (@(posedge clk) disable iff(rst) up |-> (dout == $past(dout + 1)) || (dout == 0));
  
  /////// next value must be greater than zero when up = 1 and rst = 0   
  UP_MODE_2: assert property (@(posedge clk) $fell(rst) |=> (dout != 0));   
  UP_MODE_3: assert property(@(posedge clk) $fell(rst) |-> up[->1] ##1 !$stable(dout));

  //////current value of dout must be one less than previous value when up = 0
  DOWN_MODE_1: assert property (@(posedge clk) disable iff(rst) !up |-> (dout == $past(dout - 1)) || (dout == 0) || ($past(dout) == 0));

  /////// next value must not be equal to zero when up = 0 and rst = 0   
  DOWN_MODE_2: assert property(@(posedge clk) (!up && !rst) |=> !$stable(dout));   
 
  ///////alternate way 
  property p1;
   if(up)
     ((dout == $past(dout + 1)) || (dout == 0))
     else
       ((dout == $past(dout - 1)) || (dout == 0) || ($past(dout) == 0)); 
  endproperty

  BOTH_MODE_1:assert property(@(posedge clk) !rst |-> p1);
endmodule

module tb;
  reg clk = 0,rst = 0,up = 0;
  wire [3:0] dout;
  reg temp = 0;
  
  initial begin
    #342;
    temp = 1;
    #10;
    temp = 0;
  end
  
  counter dut (clk,rst,up,dout); 
  
  bind counter counter_assert dut2(clk, rst, up, dout);
    
  always #5 clk = ~clk;
  
  initial begin
    rst = 1;
    #30;
    rst = 0;
    up = 1;
    #200;
    up = 0;
    rst = 1;
    #25;
    rst = 0;
    
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #360;
    $finish;
  end
endmodule
```

## Assertions in FIFO
```
/////////////////////////////////////////////Testbench Code
 
module assert_fifo (
  input clk, rst, wr, rd, 
  input [7:0] din,input [7:0] dout,
  input empty, full
);
	
    // (1) status of full and empty when rst asserted
    ////check on edge
	RST_1: assert property (@(posedge clk) $rose(rst) |-> (full == 1'b0 && empty == 1'b1))$info("A1 Suc at %0t",$time);
   
	/////check on level
 	RST_2: assert property (@(posedge clk) rst |-> (full == 1'b0 && empty == 1'b1))$info("A2 Suc at %0t",$time);  
 
  
	//  (2) operation of full and empty flag
    FULL_1:  assert property (@(posedge clk) disable iff(rst) $rose(full) |=> (FIFO.wptr == 0)[*1:$] ##1 !full)$info("full Suc at %0t",$time); 
    FULL_2:  assert property (@(posedge clk) disable iff(rst) (FIFO.cnt == 15) |-> full)$info("full Suc at %0t",$time);
	EMPTY_1: assert property (@(posedge clk) disable iff(rst) $rose(empty) |=> (FIFO.rptr == 0)[*1:$] ##1 !empty)$info("full Suc at %0t",$time); 
  	EMPTY_2: assert property (@(posedge clk) disable iff(rst) (FIFO.cnt == 0) |-> empty)$info("empty Suc at %0t",$time); 

    ///////  (3) read while empty
    READ_EMPTY: assert property (@(posedge clk) disable iff(rst) empty |-> !rd)$info("Suc at %0t",$time);  
 
    ////////// (4) Write while FULL     
    WRITE_FULL: assert property (@(posedge clk) disable iff(rst) full |-> !wr)$info("Suc at %0t",$time);
  
      
    ////////////// (5) Write+Read pointer behavior with rd and wr signal      
    //////if wr high and full is low, wptr must incr       
  	WPTR1: assert property (@(posedge clk)  !rst && wr && !full |=> $changed(FIFO.wptr));
         
    //////// if wr is low, wptr must constant
  	WPTR2: assert property (@(posedge clk) !rst && !wr |=> $stable(FIFO.wptr));
    
    /////// if rd is high, wptr must stay constant
  	WPTR3: assert property (@(posedge clk) !rst && rd |=> $stable(FIFO.wptr)) ;            
    RPTR1: assert property (@(posedge clk) !rst && rd && !empty |=> $changed(FIFO.rptr));
    RPTR2: assert property (@(posedge clk) !rst && !rd |=> $stable(FIFO.rptr));
    RPTR3: assert property (@(posedge clk) !rst && wr |=> $stable(FIFO.rptr));

    //////////  (6) state of all the i/o ports for all clock edge
  	always@(posedge clk)
      begin
        assert (!$isunknown(dout));
        assert (!$isunknown(rst));
        assert (!$isunknown(wr));
        assert (!$isunknown(rd));
        assert (!$isunknown(din));
      end

    //////////////////// (7) Data must match
    property p1;
      integer waddr;
      logic [7:0] data;

      (wr, waddr = tb.i, data = din) |-> ##[1:30] rd ##0 (waddr == tb.i - 1, $display("din: %0d dout :%0d",data, dout));
    endproperty
  
  	assert property (@(posedge clk) disable iff(rst) p1) $info("Suc at %0t",$time);
endmodule

//////////////////////////////////////////////////////////////////////////////////////////////

module tb;
  reg clk = 0, rst = 0, wr = 0, rd = 0;
  reg [7:0] din = 0;
  wire [7:0] dout;
  wire empty, full;
  integer i = 0;
  reg start = 0;
  
  initial begin
    #2;
    start = 1;
    #10;
    start = 0;
  end

  reg temp = 0;
  initial begin
    #292;
    temp = 1;
    #10;
    temp = 0;
  end
  
  FIFO dut (clk,rst,wr,rd,din,dout,empty,full);
  bind FIFO assert_fifo dut2 (clk,rst,wr,rd,din,dout,empty,full);

  always #5 clk = ~clk;
  
  task write();
    for( i = 0; i < 15; i++)
      begin   
        din = $urandom();
        wr = 1'b1;
        rd = 1'b0;
        @(posedge clk);
      end
  endtask

  task read();
    for( i = 0; i < 15; i++)
      begin           
        wr = 1'b0;
        rd = 1'b1;
        @(posedge clk);
      end
  endtask
 
  initial begin
    @(posedge clk) {rst,wr,rd} = 3'b100;
    @(posedge clk) {rst,wr,rd} = 3'b101;
    @(posedge clk) {rst,wr,rd} = 3'b110;
    @(posedge clk) {rst,wr,rd} = 3'b111;
    @(posedge clk) {rst,wr,rd} = 3'b000; 
    
    write();
    @(posedge clk) {rst,wr,rd} = 3'b010;
    @(posedge clk);
    
    read();  
  end

  /*
  initial begin
 
    $display("------------Starting Test-----------------");
    $display("------(1) Behavior of FULL and EMPTY on RST High------");
    @(posedge clk) {rst,wr,rd} = 3'b100;
    @(posedge clk) {rst,wr,rd} = 3'b101;
    @(posedge clk) {rst,wr,rd} = 3'b110;
    @(posedge clk) {rst,wr,rd} = 3'b111;
    @(posedge clk) {rst,wr,rd} = 3'b000;
    @(posedge clk);
    #20;
 
    $display("------(2) Reading from Empty FIFO------");
    @(posedge clk) {rst,wr,rd} = 3'b001;
    @(posedge clk);
    
    #20;
    $display("------(3) Writing Data to FULL FIFO------");
    $display("--------(4) RPTR and WPTR behavior during Writing--------");
    write();
    @(posedge clk) {rst,wr,rd} = 3'b010;
    @(posedge clk);
    
    #20;
    $display("--------(5) RPTR and WPTR behavior during reading--------");
    read();

  end
  */

  //// ---------------- (6) Data Matched during read and write operation
  /*
  initial begin
    write();
    repeat(5) @(posedge clk);
    read(); 
  end
  
 */ 

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0);
    #500;
    $finish();
  end
  
endmodule
```

## Assertions in SystemVerilog based testbench environment
