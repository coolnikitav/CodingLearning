# Fundamentals

## Bins
- Q: What is a coverpoint? What is a covergroup?

![image](https://github.com/user-attachments/assets/b434c8cb-0f0e-44b0-8525-ad8d88b17998)

## Covergroup without event
- Q: Write verilog code for a buffer.
- Q: Write a testbench where you apply an input 10 times. Include coverpoints and covergroups. Make them manual(not triggered by events).

```
module buffer(
  input [1:0] a,
  output [1:0] b
);
	assign b = a;
endmodule
```
```
module tb;
  reg [1:0] a;
  wire [1:0] b;
  integer i = 0;
  
  buffer dut(.a(a), .b(b));
  
  covergroup cvr_a;  // manual sample method if don't provide event
    coverpoint a;  // auto bins because we did not specify
    coverpoint b;
  endgroup
  
  cvr_a ci = new();
  
  initial begin
    for (i = 0; i < 10; i++) begin
      a = $urandom();
      ci.sample();
      #10;
    end
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #500;
    $finish();
  end
endmodule
```
Note: the code does not achieve 100% coverage

## Coverage with event
- Q: Now modify the testbench to have covergroup triggered by event.

```
module tb;
  reg [1:0] a;
  wire [1:0] b;
  integer i = 0;
  
  buffer dut(.a(a), .b(b));
  
  covergroup cvr_a @(a);  // when signal a changes
    coverpoint a;  // auto bins because we did not specify
    coverpoint b;
  endgroup
  
  cvr_a ci = new();
  
  initial begin
    for (i = 0; i < 10; i++) begin
      a = $urandom();
      #10;
    end
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #500;
    $finish();
  end
endmodule
```
Note: the code does not achieve 100% coverage

## Understanding Covergroup Options
- Q: Name 5 options and explain what they do.
  
![image](https://github.com/user-attachments/assets/7a3b3cc3-2a14-433d-8963-16a657a28216)

```
covergroup cvr_a @(a);  
    option.per_instance = 1; // ON
    option.name = "COVER_A_B";
    option.goal = 50;
    option.at_least = 4;
    option.auto_bin_max = 2;  // default value is 64
    
    coverpoint a;  
    coverpoint b;
  endgroup
```
```
 COVERGROUP COVERAGE
#     ============================================================
#     |       Covergroup        |  Hits   |  Goal /  |  Status   |
#     |                         |         | At Least |           |
#     ============================================================
#     | TYPE /tb/cvr_a          | 50.000% | 100.000% | Uncovered |
#     ============================================================
#     | INSTANCE COVER_A_B      | 50.000% |  50.000% | Covered   |
#     |-------------------------|---------|----------|-----------|
#     | COVERPOINT COVER_A_B::a | 50.000% | 100.000% | Uncovered |
#     |-------------------------|---------|----------|-----------|
#     | bin auto[0:1]           |       4 |        4 | Covered   |
#     | bin auto[2:3]           |       3 |        4 | Uncovered |
#     |-------------------------|---------|----------|-----------|
#     | COVERPOINT COVER_A_B::b | 50.000% | 100.000% | Uncovered |
#     |-------------------------|---------|----------|-----------|
#     | bin auto[0:1]           |       4 |        4 | Covered   |
#     | bin auto[2:3]           |       3 |        4 | Uncovered |
#     ============================================================
```

## Understanding weight
- Q: How to assign weight to a coverpoint?

```
covergroup cvr_a;  // manual sample method
    option.per_instance = 1; // ON
    
    coverpoint a {
     option.weight = 3;
    }
    coverpoint b {
     option.weight = 5; 
    }
  endgroup
```
```
WEIGHTED AVERAGE: 65.625%
# 
# 
#     COVERGROUP COVERAGE
#     =============================================================
#     |        Covergroup        |  Hits   |  Goal /  |  Status   |
#     |                          |         | At Least |           |
#     =============================================================
#     | TYPE /tb/cvr_a           | 65.625% | 100.000% | Uncovered |
#     =============================================================
#     | INSTANCE <UNNAMED1>      | 65.625% | 100.000% | Uncovered |
#     |--------------------------|---------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::a | 50.000% | 100.000% | Uncovered |
#     |--------------------------|---------|----------|-----------|
#     | bin auto[0]              |       2 |        1 | Covered   |
#     | bin auto[1]              |       3 |        1 | Covered   |
#     | bin auto[2]              |       0 |        1 | Zero      |
#     | bin auto[3]              |       0 |        1 | Zero      |
#     |--------------------------|---------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::b | 75.000% | 100.000% | Uncovered |
#     |--------------------------|---------|----------|-----------|
#     | bin auto[0]              |       1 |        1 | Covered   |
#     | bin auto[1]              |       1 |        1 | Covered   |
#     | bin auto[2]              |       3 |        1 | Covered   |
#     | bin auto[3]              |       0 |        1 | Zero      |
#     =============================================================
```

## Understanding option and type_option
- Q: Set a goal for the coverage type.
  
Use option for coverpoint and covergroup. Use type_option for coverage type.

coverage type
- covergroup
  - coverpoint
 
```
covergroup cvr_a;  // manual sample method
    option.per_instance = 1; // ON
    option.goal = 50;
    type_option.goal = 62;
    
    coverpoint a {
     option.goal = 50; 
    }
    coverpoint b {
     option.goal = 75; 
    }
  endgroup

===========================================================
#     | TYPE /tb/cvr_a           | 62.500% |  62.000% | Covered |
#     ===========================================================
#     | INSTANCE <UNNAMED1>      | 62.500% |  50.000% | Covered |
#     |--------------------------|---------|----------|---------|
#     | COVERPOINT <UNNAMED1>::a | 50.000% |  50.000% | Covered |
#     |--------------------------|---------|----------|---------|
#     | bin auto[0]              |       2 |        1 | Covered |
#     | bin auto[1]              |       3 |        1 | Covered |
#     | bin auto[2]              |       0 |        1 | Zero    |
#     | bin auto[3]              |       0 |        1 | Zero    |
#     |--------------------------|---------|----------|---------|
#     | COVERPOINT <UNNAMED1>::b | 75.000% |  75.000% | Covered |
#     |--------------------------|---------|----------|---------|
#     | bin auto[0]              |       1 |        1 | Covered |
#     | bin auto[1]              |       1 |        1 | Covered |
#     | bin auto[2]              |       3 |        1 | Covered |
#     | bin auto[3]              |       0 |        1 | Zero    |
#     ===========================================================
```

## Turning on/off Coverage with Specific Conditions
The a values when rst = 1 do not count:

```
module tb;
  reg [1:0] a = 0;
  reg rst = 0;
  integer i = 0;
    
  initial begin
    rst = 1;
    #30;
    rst = 0;
  end
  
  covergroup c;
    option.per_instance = 1;
    
    coverpoint a iff (!rst);
  endgroup
  
  initial begin
    c ci = new();
    for (i = 0; i < 10; i++) begin
      a = $urandom();
      ci.sample();
      #10;
    end
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #500;
    $finish();
  end
endmodule

 COVERGROUP COVERAGE
#     =============================================================
#     |        Covergroup        |  Hits   |  Goal /  |  Status   |
#     |                          |         | At Least |           |
#     =============================================================
#     | TYPE /tb/c               | 75.000% | 100.000% | Uncovered |
#     =============================================================
#     | INSTANCE <UNNAMED1>      | 75.000% | 100.000% | Uncovered |
#     |--------------------------|---------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::a | 75.000% | 100.000% | Uncovered |
#     |--------------------------|---------|----------|-----------|
#     | bin auto[0]              |       2 |        1 | Covered   |
#     | bin auto[1]              |       2 |        1 | Covered   |
#     | bin auto[2]              |       3 |        1 | Covered   |
#     | bin auto[3]              |       0 |        1 | Zero      |
#     =============================================================
```
