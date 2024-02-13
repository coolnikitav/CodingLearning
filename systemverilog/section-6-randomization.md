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
