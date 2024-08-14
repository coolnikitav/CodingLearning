# Immediate Assertions

## Different Simulation Regions and Glitches
![image](https://github.com/user-attachments/assets/456ed37e-f334-40c7-8626-7030d830617c)

Simple immediate assertion:
```
module tb;
  
 
  reg am = 0;
  reg bm = 0;
  
  wire a, b;
 
  assign a = am;
  assign b = bm;
  
 
 initial begin
   am = 1;
   bm = 1;
   #10;
   am = 0;
   bm = 1;
   #10;
   am = 1;
   bm = 0;
   #10; 
 end
  
  always_comb
  begin
  A1 : assert (a == b) $info("a and b are equal at %0t",$time);
  else $error("assertion failed at %0t",$time);
  end

 endmodule

# KERNEL: Error: testbench.sv (28): assertion failed at 0
# KERNEL: Info: testbench.sv (27): a and b are equal at 0
# KERNEL: Error: testbench.sv (28): assertion failed at 10
# KERNEL: Error: testbench.sv (28): assertion failed at 20
```

Observed deferred immediate assertion:
```
  A1 : assert #0 (a == b) $info("a and b are equal at %0t",$time);

# KERNEL: Info: testbench.sv (27): a and b are equal at 0
# KERNEL: Error: testbench.sv (28): assertion failed at 10
# KERNEL: Error: testbench.sv (28): assertion failed at 20
```

Final deferred immediate assertion:
```
  A1 : assert final (a == b) $info("a and b are equal at %0t",$time);

# KERNEL: Info: testbench.sv (27): a and b are equal at 0
# KERNEL: Error: testbench.sv (28): assertion failed at 10
# KERNEL: Error: testbench.sv (28): assertion failed at 20
```

## Format of Different Assertion Types
![image](https://github.com/user-attachments/assets/7aa7c7f9-d3fe-4e99-bef9-9cd7eea2d8d9)

## Rules for Immediate Assertions
![image](https://github.com/user-attachments/assets/903941c9-6453-4856-9da5-e8968253ec2a)

![image](https://github.com/user-attachments/assets/89c9845d-e514-49e2-8925-5437e4150409)

## Usage of Immediate Assertion in Combinational Circuit
```
module mux(
  input a,b,c,d,
  input [1:0] sel,
  output reg y
);
  
  ////adding rtl logic
  always@(*)
    begin
      case(sel)
        2'b00: y = a;
        2'b01: y = b;
        2'b10: y = ~c;
        2'b11: y = d;
      endcase
    end
 
  
  //////adding assertion checks 
  always@(*)
   begin
      case(sel)
      2'b00: y_equal_a:assert(y == a) else $error("y is not equal to a at %0t",$time);
      2'b01: y_equal_b:assert(y == b) else $error("y is not equal to b at %0t",$time);
      2'b10: y_equal_c:assert(y == c) else $error("y is not equal to c at %0t",$time);
      2'b11: y_equal_d:assert(y == d) else $error("y is not equal to d at %0t",$time); 
      endcase
    end
  
endmodule

module tb();
  reg a = 0,b = 0,c = 0 ,d = 0;
  
  reg [1:0] sel;
  wire y;
  
  
  mux dut (a,b,c,d,sel,y);
  
  
  always #5 a = ~a;
  always #10 b = ~b;
  always #15 c = ~c;
  always #20 d = ~d;
  
  initial begin
    sel = 2'b00;
    #50;
    sel = 2'b01;
    #50;
    sel = 2'b10;
    #50;
    sel = 2'b11;
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #300;
    $finish;
  end
endmodule

# KERNEL: Error: design.sv (25): y is not equal to c at 100
# KERNEL: Error: design.sv (25): y is not equal to c at 105
# KERNEL: Error: design.sv (25): y is not equal to c at 110
# KERNEL: Error: design.sv (25): y is not equal to c at 115
# KERNEL: Error: design.sv (25): y is not equal to c at 120
# KERNEL: Error: design.sv (25): y is not equal to c at 125
# KERNEL: Error: design.sv (25): y is not equal to c at 130
# KERNEL: Error: design.sv (25): y is not equal to c at 135
# KERNEL: Error: design.sv (25): y is not equal to c at 140
# KERNEL: Error: design.sv (25): y is not equal to c at 145
```

## Usage of Immediate Assertion in Sequential Circuit
```
module dff (input d,  
              input rstn,  
              input clk,  
              output q, qbar);  
  
  
    reg temp_q    = 0;
    reg temp_qbar = 1;
  
  
   always @ (posedge clk)  
    begin      
      if (!rstn) 
        begin 
          
          temp_q    <= 1'b0;
          temp_qbar <= 1'b1;
        end
       else 
         begin
          temp_q    <= d; 
          temp_qbar <= ~d;
         end
    end
 
  ////////////////////////////////////////
    always@(posedge clk)
    begin
      A1: assert (temp_q == ~temp_qbar) $info("Suc at %0t",$time);  else $info("Error at %0t", $time);
    end
    
   assign q    = temp_q;
   assign qbar = temp_qbar;
  
endmodule

module tb;
  reg d = 0;
  reg clk = 0;
  reg rstn = 0;
  wire q, qbar;
  
  dff dut (d,rstn, clk, q, qbar);
  
  always #5 clk = ~clk;
  
  always #13 d = ~d;
  
  initial begin
    rstn = 0;
    #30;
    rstn = 1;
  end
  
  
    initial begin 
    #200;
    $finish();
  end  
endmodule
```

## Disabling Assertions
![image](https://github.com/user-attachments/assets/155cfa39-691a-4aa0-9ef8-7cec3c6f2945)
