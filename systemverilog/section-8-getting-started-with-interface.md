# Getting Started with Interface

## Adding interface to a simple RTL
```
interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
endinterface

module tb;
  
  add_if aif();
  // add dut (aif.a, aif.b, aif.sum);  // positional mapping
  add dut (.a(aif.a), .b(aif.b), .sum(aif.sum));  // mapping by name
  // mapping by name is used more frequently because as the number of ports grows,
  // positional mapping becomes less reliable
  
  initial begin
    aif.a = 4;
    aif.b = 2;
    #10;
    aif.a = 3;
    #10;
    aif.b = 7;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
  
endmodule
```
## Using blocking operator for interface variables
```
interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
endinterface

module tb;
  
  add_if aif();
  add dut (.a(aif.a), .b(aif.b), .sum(aif.sum), .clk(aif.clk));  // mapping by name

  initial begin
    aif.clk = 0;
  end
  
  always #10 aif.clk = ~aif.clk;
  
  initial begin
    aif.a = 1;
    aif.b = 5;
    #22;
    aif.a = 3;
    #20;
    aif.a = 4;
    #8;
    aif.a = 5;
    #20;
    aif.a = 6;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #100;
    $finish();
  end
  
endmodule
```
## Using non-blocking operator for interface variables
```
interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
endinterface

module tb;
  
  add_if aif();
  add dut (.a(aif.a), .b(aif.b), .sum(aif.sum), .clk(aif.clk));  // mapping by name

  initial begin
    aif.clk = 0;
  end
  
  always #10 aif.clk = ~aif.clk;
  
  initial begin
    aif.a <= 1;
    aif.b <= 5;
    repeat(3) @(posedge aif.clk);
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #100;
    $finish();
  end
  
endmodule
```
## Why we prefer LOGIC over WIRE and REG in interface
- Interface with all reg type, we are not allowed to connect variable in interface to the output port of DUT
- Interface with all wire type, we are not allowed to apply stimulus using initial or always

## Adding driver code to interface
```
interface add_if;
  
  logic [3:0] a,b;
  logic [4:0] sum;
  logic clk;
  
endinterface

class driver;
  
  virtual add_if aif;  // virtual means the definition of the interface is defined outside the class
  
  task run();
    forever begin
      @(posedge aif.clk);
      aif.a <= 3;
      aif.b <= 3;
    end
  endtask
  
endclass

module tb;
  
  add_if aif();
  
  add dut (.a(aif.a),.b(aif.b),.sum(aif.sum),.clk(aif.clk));
  
  initial begin
    aif.clk <= 0;
  end
  
  always #10 aif.clk <= ~aif.clk;
  
  driver drv;
  
  initial begin
    drv = new();
    drv.aif = aif;
    drv.run();
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #100;
    $finish();
  end
  
endmodule
```
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f7504bad-4442-4740-93f6-827cc862f157)

## Adding generator
```
module add
  (
    input [3:0] a,b,
    output reg [4:0] sum,
    input clk
  );
  
  always @ (posedge clk)
    begin
      sum <= a+b;
    end
  
endmodule
```
```
class transaction;
  
 randc bit [3:0] a;
 randc bit [3:0] b;
  
  function void display();
    $display("a : %0d \t b: %0d ", a,b);
  endfunction
  
  function transaction copy();
    copy = new();
    copy.a = this.a;
    copy.b = this.b;
  endfunction
  
endclass

class generator;
  
  transaction trans;
  mailbox #(transaction) mbx;
  int i = 0;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
    trans = new();
  endfunction 
  
  task run();
    for(i = 0; i<20; i++) begin
      assert(trans.randomize()) else $display("Randomization Failed");
      $display("[GEN] : DATA SENT TO DRIVER");
      trans.display();
      mbx.put(trans.copy);
    end
  endtask

endclass

module tb;
  
  generator gen;
  mailbox #(transaction) mbx;
 
  initial begin
    mbx = new();
    gen = new(mbx);
    gen.run();
    end
 
endmodule
```
```
////////////////////////Testbench Code

class transaction;
 randc bit [3:0] a;
 randc bit [3:0] b;
  bit [4:0] sum;
  
  function void display();
    $display("a : %0d \t b: %0d \t sum : %0d",a,b,sum);
  endfunction
  
  function transaction copy();
    copy = new();
    copy.a = this.a;
    copy.b = this.b;
    copy.sum = this.sum;
  endfunction
  
endclass
 
class generator;
  
  transaction trans;
  mailbox #(transaction) mbx;
  event done;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
    trans = new();
  endfunction

  task run();
    for(int i = 0; i<10; i++) begin
      trans.randomize();
      mbx.put(trans.copy);
      $display("[GEN] : DATA SENT TO DRIVER");
      trans.display();
      #20;
    end
   -> done;
  endtask
  
endclass

interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
endinterface

class driver;
  
  virtual add_if aif;
  mailbox #(transaction) mbx;
  transaction data;
  event next;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction 

 task run();
    forever begin
      mbx.get(data);
      @(posedge aif.clk);  
      aif.a <= data.a;
      aif.b <= data.b;
      $display("[DRV] : Interface Trigger");
      data.display();
    end
  endtask

endclass
  
module tb;
  
 add_if aif();
   driver drv;
   generator gen;
   event done;
 
   mailbox #(transaction) mbx;
  
  add dut (aif.a, aif.b, aif.sum, aif.clk );

  initial begin
    aif.clk <= 0;
  end
  
  always #10 aif.clk <= ~aif.clk;
 
   initial begin
     mbx = new();
     drv = new(mbx);
     gen = new(mbx);
     drv.aif = aif;
     done = gen.done;
   end
  
  initial begin
  fork
    gen.run();
    drv.run();
  join_none
    wait(done.triggered);
    $finish();
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;  
  end
  
endmodule
```
## Important rules for SV
1) Add constructor to transaction in the custom constructor of generator
   ```
   class generator;
     transaction trans;

     function new(mailbox #(transaction) mbx);
       this.mbx = mbx;
       trans = new();
     endfunction
   endclass
   ```
   signle space for variable means correct randc behavior
2) Send deep copy of transaction object instead of original transaction object
   - Independent object for each iteration
   - Object can be used without worrying about path delay
3) Send deep copy
   - Errors coule be injected with methods/constraints
     
## Injecting error
```
class transaction;
	randc bit [3:0] a;
	randc bit [3:0] b;
    bit [4:0] sum;
  
  	function void display();
    	$display("a : %0d \t b: %0d \t sum : %0d",a,b,sum);
  	endfunction
  
  function transaction copy();
    copy = new();
    copy.a = this.a;
    copy.b = this.b;
    copy.sum = this.sum;
  endfunction
  
endclass

class error extends transaction;
  constraint data_c { a == 0; b == 0;}
endclass
 
class generator;
  
  transaction trans;
  mailbox #(transaction) mbx;
  event done;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
    trans = new();
  endfunction

  task run();
    for(int i = 0; i<10; i++) begin
      trans.randomize();
      mbx.put(trans.copy);
      $display("[GEN] : DATA SENT TO DRIVER");
      trans.display();
      #20;
    end
   -> done;
  endtask
  
endclass

interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
  
  modport DRV (input a,b, input sum,clk);
endinterface

class driver;
  
  virtual add_if aif;
  mailbox #(transaction) mbx;
  transaction data;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction 

 task run();
    forever begin
      mbx.get(data);
      @(posedge aif.clk);  
      aif.a <= data.a;
      aif.b <= data.b;
      $display("[DRV] : Interface Trigger");
      data.display();
    end
  endtask

endclass
  
module tb;
  
  add_if aif();
  driver drv;
  generator gen;
  error err;
  
  event done;
 
  mailbox #(transaction) mbx;
  
  add dut (aif.a, aif.b, aif.sum, aif.clk );

  initial begin
    aif.clk <= 0;
  end
  
  always #10 aif.clk <= ~aif.clk;
 
   initial begin
     mbx = new();
     err = new();
     drv = new(mbx);
     gen = new(mbx);
     
     gen.trans = err;
     
     drv.aif = aif;
     done = gen.done;
   end
  
  initial begin
    fork
      gen.run();
      drv.run();
    join_none
    wait(done.triggered);
    $finish();
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;  
  end
  
endmodule
```
```
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
```
```
class transaction;
	randc bit [3:0] a;
	randc bit [3:0] b;
    bit [4:0] sum;
  
  	function void display();
    	$display("a : %0d \t b: %0d \t sum : %0d",a,b,sum);
  	endfunction
  
  virtual function transaction copy();
    copy = new();
    copy.a = this.a;
    copy.b = this.b;
    copy.sum = this.sum;
  endfunction
  
endclass

class error extends transaction;
  //constraint data_c { a == 0; b == 0;}
  
  function transaction copy();
    copy = new();
    copy.a = 0;
    copy.b = 0;
    copy.sum = this.sum;
  endfunction
endclass
 
class generator;
  
  transaction trans;
  mailbox #(transaction) mbx;
  event done;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
    trans = new();
  endfunction

  task run();
    for(int i = 0; i<10; i++) begin
      trans.randomize();
      mbx.put(trans.copy);
      $display("[GEN] : DATA SENT TO DRIVER");
      trans.display();
      #20;
    end
   -> done;
  endtask
  
endclass

interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
  
  modport DRV (input a,b, input sum,clk);
endinterface

class driver;
  
  virtual add_if aif;
  mailbox #(transaction) mbx;
  transaction data;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction 

 task run();
    forever begin
      mbx.get(data);
      @(posedge aif.clk);  
      aif.a <= data.a;
      aif.b <= data.b;
      $display("[DRV] : Interface Trigger");
      data.display();
    end
  endtask

endclass
  
module tb;
  
  add_if aif();
  driver drv;
  generator gen;
  error err;
  
  event done;
 
  mailbox #(transaction) mbx;
  
  add dut (aif.a, aif.b, aif.sum, aif.clk );

  initial begin
    aif.clk <= 0;
  end
  
  always #10 aif.clk <= ~aif.clk;
 
   initial begin
     mbx = new();
     err = new();
     drv = new(mbx);
     gen = new(mbx);
     
     gen.trans = err;
     
     drv.aif = aif;
     done = gen.done;
   end
  
  initial begin
    fork
      gen.run();
      drv.run();
    join_none
    wait(done.triggered);
    $finish();
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;  
  end
  
endmodule
```
```
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 14 	 b: 14 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 6 	 b: 1 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 1 	 b: 0 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 4 	 b: 15 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 3 	 b: 8 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 7 	 b: 4 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 0 	 b: 9 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 15 	 b: 10 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 13 	 b: 5 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [GEN] : DATA SENT TO DRIVER
# KERNEL: a : 10 	 b: 2 	 sum : 0
# KERNEL: [DRV] : Interface Trigger
# KERNEL: a : 0 	 b: 0 	 sum : 0
```

## Adding monitor and scoreboard
```
// will send transaction class between monitor and scoreboard
class transaction;
	randc bit [3:0] a;
	randc bit [3:0] b;
    bit [4:0] sum;
  
  	function void display();
    	$display("a : %0d \t b: %0d \t sum : %0d",a,b,sum);
  	endfunction
  
endclass

interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
endinterface

class monitor;
  mailbox #(transaction) mbx;
  transaction trans;
  virtual add_if aif;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
  	forever begin
      trans = new();
      @(posedge aif.clk); 
      // we only need non-blocking if we are assigning values to interface
      trans.a = aif.a;
      trans.b = aif.b;
      trans.sum = aif.sum;
      $display("[MON] : DATA SENT TO SCOREBOARD");
      trans.display();
      mbx.put(trans);
    end
  endtask
endclass

class scoreboard;
  mailbox #(transaction) mbx;
  transaction trans;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
    forever begin
      mbx.get(trans);
      $display("[SCO] : DATA RCVD FROM MONITOR");
      trans.display();
      #20;
    end
  endtask
endclass

module tb;
  
  add_if aif();
  monitor mon;
  scoreboard sco;
  mailbox #(transaction) mbx;

  add dut (aif.a, aif.b, aif.sum, aif.clk );

  initial begin
    aif.clk <= 0;
  end
  
  always #10 aif.clk <= ~aif.clk;
 
  initial begin
    for (int i = 0; i < 20; i++) begin
      @(posedge aif.clk);
      aif.a <= $urandom_range(0,15);
      aif.b <= $urandom_range(0,15);
    end
  end
  
  initial begin
    mbx = new();
    mon = new(mbx);
    sco = new(mbx);
    mon.aif = aif;
  end
  
  initial begin
    fork
      mon.run();
      sco.run();
    join
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;  
    #450;
    $finish();
  end
  
endmodule
```
```
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 3 	 b: 11 	 sum : 0
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 3 	 b: 11 	 sum : 0
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 3 	 sum : 14
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 3 	 sum : 14
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 4 	 b: 9 	 sum : 14
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 4 	 b: 9 	 sum : 14
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 15 	 b: 15 	 sum : 13
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 15 	 b: 15 	 sum : 13
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 4 	 b: 1 	 sum : 30
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 4 	 b: 1 	 sum : 30
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 10 	 b: 12 	 sum : 5
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 10 	 b: 12 	 sum : 5
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 9 	 sum : 22
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 9 	 sum : 22
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 5 	 b: 15 	 sum : 20
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 5 	 b: 15 	 sum : 20
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 13 	 sum : 20
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 13 	 sum : 20
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 14 	 b: 9 	 sum : 24
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 14 	 b: 9 	 sum : 24
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 8 	 b: 3 	 sum : 23
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 8 	 b: 3 	 sum : 23
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 15 	 b: 4 	 sum : 11
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 15 	 b: 4 	 sum : 11
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 10 	 b: 2 	 sum : 19
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 10 	 b: 2 	 sum : 19
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 15 	 b: 0 	 sum : 12
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 15 	 b: 0 	 sum : 12
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 0 	 b: 4 	 sum : 15
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 0 	 b: 4 	 sum : 15
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 7 	 b: 14 	 sum : 4
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 7 	 b: 14 	 sum : 4
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 8 	 b: 10 	 sum : 21
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 8 	 b: 10 	 sum : 21
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 8 	 b: 10 	 sum : 18
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 8 	 b: 10 	 sum : 18
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 13 	 b: 15 	 sum : 18
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 13 	 b: 15 	 sum : 18
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 15 	 sum : 28
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 15 	 sum : 28
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 15 	 sum : 26
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 15 	 sum : 26
```
```
// will send transaction class between monitor and scoreboard
class transaction;
	randc bit [3:0] a;
	randc bit [3:0] b;
    bit [4:0] sum;
  
  	function void display();
    	$display("a : %0d \t b: %0d \t sum : %0d",a,b,sum);
  	endfunction
  
endclass

interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
endinterface

class monitor;
  mailbox #(transaction) mbx;
  transaction trans;
  virtual add_if aif;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
  	forever begin
      trans = new();
      repeat (2) @(posedge aif.clk); 
      // we only need non-blocking if we are assigning values to interface
      trans.a = aif.a;
      trans.b = aif.b;
      trans.sum = aif.sum;
      $display("[MON] : DATA SENT TO SCOREBOARD");
      trans.display();
      mbx.put(trans);
    end
  endtask
endclass

class scoreboard;
  mailbox #(transaction) mbx;
  transaction trans;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
    forever begin
      mbx.get(trans);
      $display("[SCO] : DATA RCVD FROM MONITOR");
      trans.display();
      #40;
    end
  endtask
endclass

module tb;
  
  add_if aif();
  monitor mon;
  scoreboard sco;
  mailbox #(transaction) mbx;

  add dut (aif.a, aif.b, aif.sum, aif.clk );

  initial begin
    aif.clk <= 0;
  end
  
  always #10 aif.clk <= ~aif.clk;
 
  initial begin
    for (int i = 0; i < 20; i++) begin
      repeat(2) @(posedge aif.clk);
      aif.a <= $urandom_range(0,15);
      aif.b <= $urandom_range(0,15);
    end
  end
  
  initial begin
    mbx = new();
    mon = new(mbx);
    sco = new(mbx);
    mon.aif = aif;
  end
  
  initial begin
    fork
      mon.run();
      sco.run();
    join
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;  
    #450;
    $finish();
  end
  
endmodule
```
```
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 3 	 b: 11 	 sum : 14
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 3 	 b: 11 	 sum : 14
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 3 	 sum : 14
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 3 	 sum : 14
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 4 	 b: 9 	 sum : 13
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 4 	 b: 9 	 sum : 13
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 15 	 b: 15 	 sum : 30
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 15 	 b: 15 	 sum : 30
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 4 	 b: 1 	 sum : 5
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 4 	 b: 1 	 sum : 5
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 10 	 b: 12 	 sum : 22
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 10 	 b: 12 	 sum : 22
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 9 	 sum : 20
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 9 	 sum : 20
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 5 	 b: 15 	 sum : 20
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 5 	 b: 15 	 sum : 20
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 13 	 sum : 24
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 13 	 sum : 24
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 14 	 b: 9 	 sum : 23
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 14 	 b: 9 	 sum : 23
```
## Adding a scoreboard model
```
// will send transaction class between monitor and scoreboard
class transaction;
	randc bit [3:0] a;
	randc bit [3:0] b;
    bit [4:0] sum;
  
  	function void display();
    	$display("a : %0d \t b: %0d \t sum : %0d",a,b,sum);
  	endfunction
  
endclass

interface add_if;
  logic [3:0] a;
  logic [3:0] b;
  logic [4:0] sum;
  logic clk;
endinterface

class monitor;
  mailbox #(transaction) mbx;
  transaction trans;
  virtual add_if aif;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
  	forever begin
      trans = new();
      repeat (2) @(posedge aif.clk); 
      // we only need non-blocking if we are assigning values to interface
      trans.a = aif.a;
      trans.b = aif.b;
      trans.sum = aif.sum;
      $display("----------------------------");
      $display("[MON] : DATA SENT TO SCOREBOARD");
      trans.display();
      mbx.put(trans);
    end
  endtask
endclass

class scoreboard;
  mailbox #(transaction) mbx;
  transaction trans;
  
  function new(mailbox #(transaction) mbx);
    this.mbx = mbx;
  endfunction
  
  task compare(input transaction trans);
    if( (trans.sum) == (trans.a + trans.b) )
      $display("[SCO] : SUM RESULT MATCHED");
    else
      $error("[SCO] : SUM RESULT MISMATCHED");  // $warning will give a warning, $fatal will stop the simulation
  endtask
  
  task run();
    forever begin
      mbx.get(trans);
      $display("[SCO] : DATA RCVD FROM MONITOR");
      trans.display();
      compare(trans);
      $display("----------------------------");
      #40;
    end
  endtask
endclass

module tb;
  
  add_if aif();
  monitor mon;
  scoreboard sco;
  mailbox #(transaction) mbx;

  add dut (aif.a, aif.b, aif.sum, aif.clk );

  initial begin
    aif.clk <= 0;
  end
  
  always #10 aif.clk <= ~aif.clk;
 
  initial begin
    for (int i = 0; i < 20; i++) begin
      repeat(2) @(posedge aif.clk);
      aif.a <= $urandom_range(0,15);
      aif.b <= $urandom_range(0,15);
    end
  end
  
  initial begin
    mbx = new();
    mon = new(mbx);
    sco = new(mbx);
    mon.aif = aif;
  end
  
  initial begin
    fork
      mon.run();
      sco.run();
    join
  end

  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;  
    #450;
    $finish();
  end
  
endmodule
```
```
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 0 	 b: 0 	 sum : 0
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 3 	 b: 11 	 sum : 14
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 3 	 b: 11 	 sum : 14
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 3 	 sum : 14
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 3 	 sum : 14
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 4 	 b: 9 	 sum : 13
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 4 	 b: 9 	 sum : 13
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 15 	 b: 15 	 sum : 30
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 15 	 b: 15 	 sum : 30
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 4 	 b: 1 	 sum : 5
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 4 	 b: 1 	 sum : 5
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 10 	 b: 12 	 sum : 22
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 10 	 b: 12 	 sum : 22
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 9 	 sum : 20
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 9 	 sum : 20
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 5 	 b: 15 	 sum : 20
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 5 	 b: 15 	 sum : 20
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 11 	 b: 13 	 sum : 24
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 11 	 b: 13 	 sum : 24
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
# KERNEL: ----------------------------
# KERNEL: [MON] : DATA SENT TO SCOREBOARD
# KERNEL: a : 14 	 b: 9 	 sum : 23
# KERNEL: [SCO] : DATA RCVD FROM MONITOR
# KERNEL: a : 14 	 b: 9 	 sum : 23
# KERNEL: [SCO] : SUM RESULT MATCHED
# KERNEL: ----------------------------
```
