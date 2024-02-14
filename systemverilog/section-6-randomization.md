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
