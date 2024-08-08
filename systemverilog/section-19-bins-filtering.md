# Bins Filtering

## Fundamentals
- Q: What is "with" clause?
- Q: What are illegal bins?
- Q: What are ignore bins?
- Q: What are wildcard bins?

- With clause - allows creation of the bins if condition specified with the clause matches
```
bit [3:0] a;

coverpoint a {
  bins used_a[] = a with (item % 2 == 0);  // 0 2 4 6 8 10 12 14
}


coverpoint a {
  bins used_a[] = [1:10] with (item % 2 == 0);  // 2 4 6 8 10
}
```

- Illegal bins - set of values of variable excluded from coverage if marked illegal. Throw error if illegal values are applied
```
coverpoint a {
  illegal_bins unused_a = {2,3};
}
```

- Ignore bins - specified values with ignore bins are excluded from the code coverage. Do not throw error if send ignore bins to the variable.
```
coverpoint a {
  ignore_bins unused_a = {2,3};
}
```

- Wildcard bins - values of few bits from the vector do not affect functionality
```
coverpoint a {
  wildcard bins low = {2'b0?}; // will include 00, 01 hits
}
```

## Bins Filtering: With
```
module tb;
  reg [3:0] a; 
  integer i = 0;
  
  covergroup c;
  	option.per_instance = 1;
    coverpoint a {
      bins zero = {0};
      bins odd_a = a with ((item > 0) && (item % 2 == 1)); 
      bins even_a = a with ((item > 0) && (item % 2 == 0)); 
      bins mul_3 = a with ((item > 0) && (item % 3 == 0));
    }
  endgroup
  
  c ci;
  
  initial begin
    ci = new();
    
    for (int i = 0; i < 10; i++) begin
      a = $urandom();
      $display("Value of a : %0d", a);
      ci.sample();
      #10;
    end
  end
  
endmodule
```
```
module tb;
  reg [3:0] a; 
  reg [6:0] btemp;
  integer i = 0;
  int b;
  
  covergroup c;
  	option.per_instance = 1;
    coverpoint b {
      bins zero = {0};
      bins bdiv5[] =  {[1:100]} with (item % 5 == 0);
    }
  endgroup
  
  c ci;
  
  initial begin
    ci = new();
    
    for (int i = 0; i < 1000; i++) begin
      btemp = $urandom();  // most values generated will be much greater than 100
      b = btemp;
      $display("Value of b : %0d", b);
      ci.sample();
    end
  end
  
endmodule

#     COVERGROUP COVERAGE
#     ============================================================
#     |        Covergroup        |   Hits   |  Goal /  | Status  |
#     |                          |          | At Least |         |
#     ============================================================
#     | TYPE /tb/c               | 100.000% | 100.000% | Covered |
#     ============================================================
#     | INSTANCE <UNNAMED1>      | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::b | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | bin zero                 |        8 |        1 | Covered |
#     | bin bdiv5[5]             |       11 |        1 | Covered |
#     | bin bdiv5[10]            |        6 |        1 | Covered |
#     | bin bdiv5[15]            |       11 |        1 | Covered |
#     | bin bdiv5[20]            |       12 |        1 | Covered |
#     | bin bdiv5[25]            |        3 |        1 | Covered |
#     | bin bdiv5[30]            |        7 |        1 | Covered |
#     | bin bdiv5[35]            |        7 |        1 | Covered |
#     | bin bdiv5[40]            |       12 |        1 | Covered |
#     | bin bdiv5[45]            |        7 |        1 | Covered |
#     | bin bdiv5[50]            |        8 |        1 | Covered |
#     | bin bdiv5[55]            |        6 |        1 | Covered |
#     | bin bdiv5[60]            |       10 |        1 | Covered |
#     | bin bdiv5[65]            |       10 |        1 | Covered |
#     | bin bdiv5[70]            |       10 |        1 | Covered |
#     | bin bdiv5[75]            |        5 |        1 | Covered |
#     | bin bdiv5[80]            |        9 |        1 | Covered |
#     | bin bdiv5[85]            |        7 |        1 | Covered |
#     | bin bdiv5[90]            |       11 |        1 | Covered |
#     | bin bdiv5[95]            |       12 |        1 | Covered |
#     | bin bdiv5[100]           |        7 |        1 | Covered |
#     ============================================================
```

## Understanding illegal_bins
Values of 6 and 7 should be excluded:
```
module tb;
  reg [2:0] opcode;
  reg [2:0] a,b;
  reg [3:0] res;
  integer i = 0;
  
  always_comb begin
    case (opcode)
      0: res = a + b;
      1: res = a - b;
      2: res = a;
      3: res = b;
      4: res = a & b;
      5: res = a | b;    
      default: res = 0;
    endcase
  end
  
  covergroup c;
    option.per_instance = 1;
    coverpoint opcode {
      bins valid_opcode[] = {[0:5]};
      illegal_bins invalid_opcode[] = {[6:7]};
    }
  endgroup
  
  c ci;
  
  initial begin
    ci = new();
    
    for (i = 0; i < 50; i++) begin
      opcode = $urandom();      
      ci.sample();
    end
  end
endmodule

# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[7]' was hit with value '7' at iteration #1 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[6]' was hit with value '6' at iteration #6 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[6]' was hit with value '6' at iteration #9 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[7]' was hit with value '7' at iteration #12 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[7]' was hit with value '7' at iteration #22 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[7]' was hit with value '7' at iteration #23 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[6]' was hit with value '6' at iteration #24 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[7]' was hit with value '7' at iteration #26 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[6]' was hit with value '6' at iteration #34 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[6]' was hit with value '6' at iteration #44 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# ACDB: Error: ACDB_0012 testbench.sv (23): Illegal bin 'invalid_opcode[7]' was hit with value '7' at iteration #45 of covergroup sampling. It will have no impact on the coverage statistics. HDL instance: "/tb". Covergroup type: "c", covergroup instance: "<UNNAMED1>", coverpoint: "opcode".
# KERNEL: Simulation has finished. There are no more test vectors to simulate.

COVERGROUP COVERAGE
#     ==================================================================
#     |          Covergroup           |   Hits   |  Goal /  |  Status  |
#     |                               |          | At Least |          |
#     ==================================================================
#     | TYPE /tb/c                    | 100.000% | 100.000% | Covered  |
#     ==================================================================
#     | INSTANCE <UNNAMED1>           | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::opcode | 100.000% | 100.000% | Covered  |
#     |-------------------------------|----------|----------|----------|
#     | bin valid_opcode[0]           |        6 |        1 | Covered  |
#     | bin valid_opcode[1]           |       11 |        1 | Covered  |
#     | bin valid_opcode[2]           |        5 |        1 | Covered  |
#     | bin valid_opcode[3]           |        6 |        1 | Covered  |
#     | bin valid_opcode[4]           |        9 |        1 | Covered  |
#     | bin valid_opcode[5]           |        2 |        1 | Covered  |
#     | illegal bin invalid_opcode[6] |        5 |    -     | Occurred |
#     | illegal bin invalid_opcode[7] |        6 |    -     | Occurred |
#     ==================================================================
# 
```
