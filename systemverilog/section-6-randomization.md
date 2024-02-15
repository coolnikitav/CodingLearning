# Randomization

## Generator
```
// transaction
// generator

class generator;
  // rand lets values repeat
  // randc doesn't let values repeat
  rand bit [3:0] a,b;  // rand or randc
  bit [3:0] y;
  
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    for (i=0; i<10; i++) begin
      g.randomize();
      $display("value of a : %0d and b : %0d", g.a,g.b);
      #10;
    end
  end
  
endmodule
```

### Checking if randomization is successful: IF ELSE
```
// transaction
// generator

class generator;
  // rand lets values repeat
  // randc doesn't let values repeat
  rand bit [3:0] a,b;  // rand or randc
  bit [3:0] y;
  
  constraint data {a > 15;}  // unrealistic constraint
    
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    for (i=0; i<10; i++) begin
      
      if (!g.randomize()) begin
        $display("Randomization Failed at %0t", $time);  // randomization will fail
        $finish();
      end   
      
      $display("value of a : %0d and b : %0d", g.a,g.b);
      #10;
    end
  end
  
endmodule
```
### Checking if randomization if successful: assert
```
// transaction
// generator

class generator;
  // rand lets values repeat
  // randc doesn't let values repeat
  rand bit [3:0] a,b;  // rand or randc
  bit [3:0] y;
  
  // constraint data {a > 15;}  // unrealistic constraint
    
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    for (i=0; i<10; i++) begin
      
      assert(g.randomize()) else begin
        $display("Randomization Failed at %0t", $time);
        $finish();
      end
      
      $display("value of a : %0d and b : %0d", g.a,g.b);  // randomization will succeed
      #10;
    end
  end
  
endmodule
```
```
class generator;
  rand bit [3:0] a,b;  // rand or randc
  bit [3:0] y;
    
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    for (i=0; i<10; i++) begin
      g = new();
      g.randomize();
      $display("value of a : %0d and b : %0d", g.a,g.b);
      #10;
    end
  end
  
endmodule
```

## Adding constraint: simple expression
```
class generator;
  
  randc bit [3:0] a,b;
  bit [3:0] y;
  
  constraint data_a {a > 3; a < 7;}
  
  constraint data_b {b == 3;}
  
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    for (i=0; i<10; i++) begin
      
      assert(g.randomize()) else begin
        $display("Randomization Failed at %0t", $time);
        $finish();
      end
      
      $display("value of a : %0d and b : %0d", g.a,g.b);
      #10;
    end
  end
  
endmodule
```
```
# KERNEL: value of a : 5 and b : 3
# KERNEL: value of a : 6 and b : 3
# KERNEL: value of a : 4 and b : 3
# KERNEL: value of a : 6 and b : 3
# KERNEL: value of a : 4 and b : 3
# KERNEL: value of a : 5 and b : 3
# KERNEL: value of a : 6 and b : 3
# KERNEL: value of a : 4 and b : 3
# KERNEL: value of a : 5 and b : 3
# KERNEL: value of a : 5 and b : 3
```
```
class generator;
  
  randc bit [3:0] a,b;
  bit [3:0] y;

  constraint data{a > 3; a < 7; b > 0;}
  
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    for (i=0; i<10; i++) begin
      
      assert(g.randomize()) else begin
        $display("Randomization Failed at %0t", $time);
        $finish();
      end
      
      $display("value of a : %0d and b : %0d", g.a,g.b);
      #10;
    end
  end
  
endmodule
```
```
# KERNEL: value of a : 5 and b : 10
# KERNEL: value of a : 6 and b : 2
# KERNEL: value of a : 4 and b : 9
# KERNEL: value of a : 6 and b : 4
# KERNEL: value of a : 4 and b : 5
# KERNEL: value of a : 5 and b : 14
# KERNEL: value of a : 5 and b : 12
# KERNEL: value of a : 6 and b : 8
# KERNEL: value of a : 4 and b : 1
# KERNEL: value of a : 6 and b : 6
```
## Adding constraint: working with ranges
```
class generator;
  
  randc bit [3:0] a,b;
  bit [3:0] y;

  constraint data {
    a inside {[0:8],[10:11],15};
    b inside {[3:11]};
  }
  
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    for (i=0; i<10; i++) begin
      
      assert(g.randomize()) else begin
        $display("Randomization Failed at %0t", $time);
        $finish();
      end
      
      $display("value of a : %0d and b : %0d", g.a,g.b);
      #10;
    end
  end
  
endmodule
```
```
# KERNEL: value of a : 1 and b : 5
# KERNEL: value of a : 6 and b : 10
# KERNEL: value of a : 5 and b : 8
# KERNEL: value of a : 11 and b : 9
# KERNEL: value of a : 3 and b : 6
# KERNEL: value of a : 15 and b : 4
# KERNEL: value of a : 7 and b : 7
# KERNEL: value of a : 0 and b : 3
# KERNEL: value of a : 8 and b : 11
# KERNEL: value of a : 4 and b : 7
```
```
class generator;
  
  randc bit [3:0] a,b;
  bit [3:0] y;

  constraint data {
    !(a inside {[3:7]});  // skip the range of values
    !(b inside {[5:9]});
  }
  
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    for (i=0; i<10; i++) begin
      
      assert(g.randomize()) else begin
        $display("Randomization Failed at %0t", $time);
        $finish();
      end
      
      $display("value of a : %0d and b : %0d", g.a,g.b);
      #10;
    end
  end
  
endmodule
```
## External function and constraint
```
class generator;
  
  randc bit [3:0] a,b;
  bit [3:0] y;

  extern constraint data;
  
  extern function void display();
  
endclass

constraint generator::data {
  a inside {[0:3]};
  b inside {[12:15]};
};
    
    function void generator::display();
      $display("value of a : %0d and b : %0d",a,b);
    endfunction

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    for (i=0; i<15; i++) begin
      
      assert(g.randomize()) else begin
        $display("Randomization Failed at %0t", $time);
        $finish();
      end
      
      g.display();
      #10;
    end
  end
  
endmodule
```
## Pre and post randomization methods
```
// pre-randomize
// post-randomize

class generator;
  
  randc bit [3:0] a,b;
  bit [3:0] y;

  int min;
  int max;
  
  function void pre_randomize(input int min, max);
    this.min = min;
    this.max = max;
  endfunction
  
  constraint data {
    a inside {[min:max]};
    b inside {[min:max]};
  }
  
  function void post_randomize();
    $display("value of a : %0d and b : %0d", a,b);
  endfunction
  
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    for (i=0; i<10; i++) begin
      g.pre_randomize(3,8);
      g.randomize();
      #10;
    end
  end
  
endmodule
```
## Randc buckets
```
// pre-randomize
// post-randomize

class generator;
  
  randc bit [3:0] a,b;
  bit [3:0] y;

  int min;
  int max;
  
  function void pre_randomize(input int min, max);
    this.min = min;
    this.max = max;
  endfunction
  
  constraint data {
    a inside {[min:max]};
    b inside {[min:max]};
  }
  
  function void post_randomize();
    $display("value of a : %0d and b : %0d", a,b);
  endfunction
  
endclass

module tb;
  generator g;
  int i = 0;
  
  initial begin
    g = new();
    
    $display("SPACE 1");
    g.pre_randomize(3,8);
    for (i=0; i<6; i++) begin
      g.randomize();
      #10;
    end
    $display("SPACE 2");
    g.pre_randomize(3,8);
    for (i=0; i<6; i++) begin
      g.randomize();
      #10;
    end
  end
  
endmodule
```
```
# KERNEL: SPACE 1
# KERNEL: value of a : 5 and b : 5
# KERNEL: value of a : 6 and b : 3
# KERNEL: value of a : 7 and b : 4
# KERNEL: value of a : 8 and b : 7
# KERNEL: value of a : 4 and b : 6
# KERNEL: value of a : 3 and b : 8
# KERNEL: SPACE 2
# KERNEL: value of a : 7 and b : 4
# KERNEL: value of a : 5 and b : 3
# KERNEL: value of a : 8 and b : 8
# KERNEL: value of a : 3 and b : 6
# KERNEL: value of a : 4 and b : 5
# KERNEL: value of a : 6 and b : 7
```
## Weighted distribution
:= will assign the weight to every item in the range

:/ will divide the weight equally between all of the items in the range
```
dist {0 := 10; [1:3] := 60;}
               =>
{0 := 10; 1 := 60; 2 := 60; 3 := 60;}
```
P(0) = 10/(10+60+60+60) = 10/190

P(1) = 60/190

...
```
dist {0 :/ 10; [1:3] :/ 60;}
               =>
{0 :/ 10; 1 :/ 20; 2 :/ 20; 3 :/ 20;}
```
P(0) = 10/(10+20+20+20) = 10/70

P(1) = 20/70

...
```
class first;
  
  rand bit wr;
  rand bit rd;
  
  rand bit [1:0] var1;
  rand bit [1:0] var2;
  
  constraint data {
    var1 dist {0 := 30, [1:3] := 90};
    var2 dist {0 :/ 30, [1:3] :/ 90};
  }
  
  constraint cntrl {
    wr dist {0 := 30, 1 := 70};
    rd dist {0 :/ 30, 1 :/ 70};
  }
  
endclass

module tb;
  
  first f;
  
  initial begin
    f = new();
    
    for (int i = 0; i < 100; i++) begin
      f.randomize();
      //$display("value of wr (:=) : %0d and rd (:/) : %0d", f.wr, f.rd);
      $display("value of var1 (:=) : %0d and var2 (:/) : %0d", f.var1, f.var2);
    end
  end
  
endmodule
```
## Constraint operators
- Implication
  - ->
  - (x==1)->(y==1), when x is 1, y must be 1
- Equivalence
  - <->
  - (x==1) <-> (y==1), when one of them is 1, the other one must be 1
- if else
  ```
  if ( ) {
  
  } else {

  }
  ```

### Implication operator
```
class generator;
  
  randc bit [3:0] a;
  rand bit ce;
  rand bit rst;
  
  constraint control_rst {
    rst dist {0 := 80, 1 := 20}; 
  }
  
  constraint control_ce {
    ce dist {1 := 80, 0 := 20}; 
  }
  
  constraint control_rst_ce {
    (rst == 0) -> (ce == 1); 
  }
  
endclass

module tb;
  
  generator g;
  
  initial begin
    g = new();
    
    for (int i = 0; i < 10; i++) begin
      assert(g.randomize()) else $display("Randomization failed");
      $display("value of rst : %0b and ce : %0b", g.rst, g.ce);
    end
  end
  
endmodule
```
```
# KERNEL: value of rst : 0 and ce : 1
# KERNEL: value of rst : 1 and ce : 0
# KERNEL: value of rst : 0 and ce : 1
# KERNEL: value of rst : 0 and ce : 1
# KERNEL: value of rst : 1 and ce : 1
# KERNEL: value of rst : 0 and ce : 1
# KERNEL: value of rst : 0 and ce : 1
# KERNEL: value of rst : 0 and ce : 1
# KERNEL: value of rst : 1 and ce : 1
# KERNEL: value of rst : 0 and ce : 1
```
### Equivalence operator
```
class generator;
  
  randc bit [3:0] a;
  rand bit wr;
  rand bit oe;
  
  constraint wr_c {
    wr dist {0 := 50, 1 := 50}; 
  }
  
  constraint oe_c {
    oe dist {1 := 50, 0 := 50}; 
  }
  
  constraint wr_oe_c {
    (wr == 1) <-> (oe == 0); 
  }
  
endclass

module tb;
  
  generator g;
  
  initial begin
    g = new();
    
    for (int i = 0; i < 10; i++) begin
      assert(g.randomize()) else $display("Randomization failed");
      $display("value of wr : %0b and oe : %0b", g.wr, g.oe);
    end
  end
  
endmodule
```
```
# KERNEL: value of wr : 0 and oe : 1
# KERNEL: value of wr : 1 and oe : 0
# KERNEL: value of wr : 0 and oe : 1
# KERNEL: value of wr : 0 and oe : 1
# KERNEL: value of wr : 1 and oe : 0
# KERNEL: value of wr : 1 and oe : 0
# KERNEL: value of wr : 1 and oe : 0
# KERNEL: value of wr : 0 and oe : 1
# KERNEL: value of wr : 1 and oe : 0
# KERNEL: value of wr : 0 and oe : 1
```
### IF ELSE operator
```
class generator;
  
  randc bit [3:0] raddr, waddr;
  rand bit wr;
  rand bit oe;
  
  constraint wr_c {
    wr dist {0 := 50, 1 := 50}; 
  }
  
  constraint oe_c {
    oe dist {1 := 50, 0 := 50}; 
  }
  
  constraint wr_oe_c {
    (wr == 1) <-> (oe == 0); 
  }
  
  constraint write_read {
    if (wr == 1) {
      waddr inside {[11:15]};
      raddr == 0;
    } else {
      waddr == 0;
      raddr inside {[11:15]};
    }
  }
  
endclass

module tb;
  
  generator g;
  
  initial begin
    g = new();
    
    for (int i = 0; i<15 ; i++) begin
      assert(g.randomize()) else $display("Randomization Failed");
      $display("Value of wr : %0b | oe : %0b |  raddr : %0d | waddr : %0d |", g.wr, g.oe,g.raddr, g.waddr);
    end
  end
  
endmodule
```
```
# KERNEL: Value of wr : 0 | oe : 1 |  raddr : 14 | waddr : 0 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 11 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 14 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 13 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 12 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 15 |
# KERNEL: Value of wr : 0 | oe : 1 |  raddr : 13 | waddr : 0 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 15 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 14 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 12 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 11 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 13 |
# KERNEL: Value of wr : 0 | oe : 1 |  raddr : 11 | waddr : 0 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 15 |
# KERNEL: Value of wr : 1 | oe : 0 |  raddr : 0 | waddr : 11 |
```
## Enabling/Disabling constraints
```
class generator;
  
  randc bit [3:0] raddr, waddr;
  rand bit wr;
  rand bit oe;
  
  constraint wr_c {
    wr dist {0 := 50, 1 := 50}; 
  }
  
  constraint oe_c {
    oe dist {1 := 50, 0 := 50}; 
  }
  
  constraint wr_oe_c {
    (wr == 1) <-> (oe == 0); 
  }
  
  
endclass

module tb;
  
  generator g;
  
  initial begin
    g = new();
    
    g.wr_oe_c.constraint_mode(0);  // turn constraint off
    
    $display("constraint status oe_c : %0d", g.wr_oe_c.constraint_mode());
    
    for (int i = 0; i<15 ; i++) begin
      assert(g.randomize()) else $display("Randomization Failed");
      $display("Value of wr : %0b | oe : %0b", g.wr, g.oe);
    end
  end
  
endmodule
```
```
# KERNEL: constraint status oe_c : 0
# KERNEL: Value of wr : 0 | oe : 1
# KERNEL: Value of wr : 0 | oe : 1
# KERNEL: Value of wr : 0 | oe : 1
# KERNEL: Value of wr : 1 | oe : 1
# KERNEL: Value of wr : 0 | oe : 1
# KERNEL: Value of wr : 1 | oe : 1
# KERNEL: Value of wr : 0 | oe : 1
# KERNEL: Value of wr : 0 | oe : 0
# KERNEL: Value of wr : 1 | oe : 1
# KERNEL: Value of wr : 1 | oe : 1
# KERNEL: Value of wr : 1 | oe : 0
# KERNEL: Value of wr : 1 | oe : 0
# KERNEL: Value of wr : 1 | oe : 0
# KERNEL: Value of wr : 1 | oe : 0
# KERNEL: Value of wr : 1 | oe : 1
```
## Building transaction class
```
// testbench.sv
class transaction;
  
  bit clk;
  bit rst;
  
  rand bit wreq, rreq;  // active high
  
  rand bit [7:0] wdata;
  bit [7:0] rdata;
  
  bit e;
  bit f;
  
  constraint ctrl_wr {
    wreq dist {0 := 30; 1 := 70;}; 
  }
  
  constraint ctrl_rd {
    rreq dist {0 := 30; 1 := 70;}; 
  }
  
  constraint wr_rd {
   wreq != rreq; 
  }
  
endclass
```
```
// design.sv
module fifo(
  input wreq, rreq,
  input clk,
  input rst,
  input [7:0] wdata,
  output [7:0] rdata,
  output f,e
);
  
endmodule
```
