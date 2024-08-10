# Reusable Covergroup

## Fundamentals
![image](https://github.com/user-attachments/assets/f907fc8e-e195-43f5-8787-6df60c4c9c72)

![image](https://github.com/user-attachments/assets/5b8b04a9-1c5b-43e4-b759-b73fba3bd52c)

## Pass by Reference
- Q: Write a testbech that tests all values of reg [3:0] a, b using pass by reference in covergroup.
  
```
module tb;
  reg [3:0] a, b;
  
  covergroup c (ref reg [3:0] varn, input string var_id);  // input makes it a constant
    option.per_instance = 1;
    option.name = var_id;
    coverpoint varn;
  endgroup
  
  initial begin
    c cia = new(a, "var_a");
    c cib = new(b, "var_b");
    
    for (int i = 0; i < 50; i++) begin
      a = $urandom();
      b = $urandom();
      cia.sample();
      cib.sample();
    end
  end
endmodule

#     COVERGROUP COVERAGE
#     ============================================================
#     |       Covergroup       |   Hits   |  Goal /  |  Status   |
#     |                        |          | At Least |           |
#     ============================================================
#     | TYPE /tb/c             |  96.875% | 100.000% | Uncovered |
#     ============================================================
#     | INSTANCE var_a         |  93.750% | 100.000% | Uncovered |
#     |------------------------|----------|----------|-----------|
#     | COVERPOINT var_a::varn |  93.750% | 100.000% | Uncovered |
#     |------------------------|----------|----------|-----------|
#     | bin auto[0]            |        4 |        1 | Covered   |
#     | bin auto[1]            |        6 |        1 | Covered   |
#     | bin auto[2]            |        3 |        1 | Covered   |
#     | bin auto[3]            |        3 |        1 | Covered   |
#     | bin auto[4]            |        4 |        1 | Covered   |
#     | bin auto[5]            |        4 |        1 | Covered   |
#     | bin auto[6]            |        3 |        1 | Covered   |
#     | bin auto[7]            |        2 |        1 | Covered   |
#     | bin auto[8]            |        2 |        1 | Covered   |
#     | bin auto[9]            |        5 |        1 | Covered   |
#     | bin auto[10]           |        2 |        1 | Covered   |
#     | bin auto[11]           |        0 |        1 | Zero      |
#     | bin auto[12]           |        2 |        1 | Covered   |
#     | bin auto[13]           |        6 |        1 | Covered   |
#     | bin auto[14]           |        3 |        1 | Covered   |
#     | bin auto[15]           |        1 |        1 | Covered   |
#     ============================================================
#     | INSTANCE var_b         | 100.000% | 100.000% | Covered   |
#     |------------------------|----------|----------|-----------|
#     | COVERPOINT var_b::varn | 100.000% | 100.000% | Covered   |
#     |------------------------|----------|----------|-----------|
#     | bin auto[0]            |        4 |        1 | Covered   |
#     | bin auto[1]            |        3 |        1 | Covered   |
#     | bin auto[2]            |        4 |        1 | Covered   |
#     | bin auto[3]            |        2 |        1 | Covered   |
#     | bin auto[4]            |        4 |        1 | Covered   |
#     | bin auto[5]            |        4 |        1 | Covered   |
#     | bin auto[6]            |        2 |        1 | Covered   |
#     | bin auto[7]            |        2 |        1 | Covered   |
#     | bin auto[8]            |        4 |        1 | Covered   |
#     | bin auto[9]            |        1 |        1 | Covered   |
#     | bin auto[10]           |        5 |        1 | Covered   |
#     | bin auto[11]           |        4 |        1 | Covered   |
#     | bin auto[12]           |        3 |        1 | Covered   |
#     | bin auto[13]           |        1 |        1 | Covered   |
#     | bin auto[14]           |        4 |        1 | Covered   |
#     | bin auto[15]           |        3 |        1 | Covered   |
#     ============================================================
```

## Pass By Value
- Q: Write a testbench that tests reg [3:0] a, b;  // low - 0 to 3, mid - 4 to 10, high - 11 to 15 with pass by ref and pass by val (both are used at the same time).
  
```
module tb;
  reg [3:0] a, b;  // low - 0 to 3, mid - 4 to 10, high - 11 to 15
  
  covergroup c (ref reg [3:0] varn, input int low, input int mid, input int high, input string var_id);  // input makes it a constant
    option.per_instance = 1;
    option.name = var_id;
    coverpoint varn {
      bins low_val = {[0:low]};
      bins mid_val = {[low+1:mid]};
      bins hi_val  = {[mid+1:high]};
    }
  endgroup
  
  initial begin
    c cia = new(a, 3, 10, 15, "var_a");
    c cib = new(b, 3, 10, 15, "var_b");
    
    for (int i = 0; i < 50; i++) begin
      a = $urandom();
      b = $urandom();
      cia.sample();
      cib.sample();
    end
  end
endmodule
```

## Things to remember while working with generic covergroup
```
module tb;
  reg [3:0] a;
  
  covergroup check_var (ref logic [3:0] var_name, input int var_val);
    option.per_instance = 1;
    coverpoint var_name {
      bins f[] = {[0:var_val]};
    }
  endgroup
  
  initial begin
    check_var cia = new(a, 5);
    
    for (int i = 0; i < 10; i++) begin
      a = $urandom();
      cia.sample();
    end
  end
endmodule

#     COVERGROUP COVERAGE
#     ====================================================================
#     |           Covergroup            |  Hits   |  Goal /  |  Status   |
#     |                                 |         | At Least |           |
#     ====================================================================
#     | TYPE /tb/check_var              | 50.000% | 100.000% | Uncovered |
#     ====================================================================
#     | INSTANCE <UNNAMED1>             | 50.000% | 100.000% | Uncovered |
#     |---------------------------------|---------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::var_name | 50.000% | 100.000% | Uncovered |
#     |---------------------------------|---------|----------|-----------|
#     | bin f[0]                        |       1 |        1 | Covered   |
#     | bin f[1]                        |       1 |        1 | Covered   |
#     | bin f[2]                        |       2 |        1 | Covered   |
#     | bin f[3]                        |       0 |        1 | Zero      |
#     | bin f[4]                        |       0 |        1 | Zero      |
#     | bin f[5]                        |       0 |        1 | Zero      |
#     ====================================================================
```

## Use Case 1
![image](https://github.com/user-attachments/assets/5eea9251-1962-4fa4-bcb8-62b754430894)
```
module alu
  (
    input [3:0] a,b,
    input [2:0] op,
    output reg [4:0] y
  
  );  
  
  always @(*)
    begin
      case(op)
        ///////////////arithmetic oper
        3'b000: y = a + b;
        3'b001: y = a - b;
        3'b010: y = a + 1;
        3'b011: y = b + 1;
        /////////////// logical oper
        3'b100: y = a & b;
        3'b101: y = a | b;
        3'b110: y = a ^ b;
        3'b111: y = ~a;
        
        default : y = 5'b00000;
      endcase
      
    end
endmodule

module tb;
  reg [3:0] a,b;
  reg [2:0] op;
  wire [4:0] y;
  
  covergroup cvr_in (ref reg [3:0] var_in, input int low, input int mid, input int high, input string var_id);
    option.per_instance = 1;
    option.name = var_id;
    coverpoint var_in {
      bins low_val = {[0:low]};
      bins mid_val = {[low+1:mid]};
      bins hi_val  = {[mid+1:high]};
    }
  endgroup
  
  covergroup cvr_op (ref reg [2:0] var_in, input int arithm, input int log, input string var_id);
    option.per_instance = 1;
    option.name = var_id;
    coverpoint var_in {
      bins arithmetic = {[0:arithm]};
      bins logical    = {[arithm+1:log]};
    }
  endgroup
  
  initial begin
    cvr_in cia = new(a, 3, 10, 15, "var_a");
    cvr_in cib = new(b, 3, 10, 15, "var_b");
    cvr_op cop = new(op, 3, 7, "op");
    
    for (int i = 0; i < 50; i++) begin
      a = $urandom();
      b = $urandom();
      op = $urandom();
      cia.sample();
      cib.sample();
      cop.sample();
    end
  end
endmodule

#     COVERGROUP COVERAGE
#     ============================================================
#     |        Covergroup        |   Hits   |  Goal /  | Status  |
#     |                          |          | At Least |         |
#     ============================================================
#     | TYPE /tb/cvr_in          | 100.000% | 100.000% | Covered |
#     ============================================================
#     | INSTANCE var_a           | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | COVERPOINT var_a::var_in | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | bin low_val              |       16 |        1 | Covered |
#     | bin mid_val              |       19 |        1 | Covered |
#     | bin hi_val               |       15 |        1 | Covered |
#     ============================================================
#     | INSTANCE var_b           | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | COVERPOINT var_b::var_in | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | bin low_val              |       11 |        1 | Covered |
#     | bin mid_val              |       25 |        1 | Covered |
#     | bin hi_val               |       14 |        1 | Covered |
#     ============================================================
#     | TYPE /tb/cvr_op          | 100.000% | 100.000% | Covered |
#     ============================================================
#     | INSTANCE op              | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | COVERPOINT op::var_in    | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | bin arithmetic           |       27 |        1 | Covered |
#     | bin logical              |       23 |        1 | Covered |
#     ============================================================
```

## Use Case 2
```
module tb;
  reg [3:0] addr;
  
  // lower: 0-3
  // mid: 4-11
  // high: 12-15
  
  covergroup check_addr (ref logic [3:0] var_name, input int lower, input int higher, input string instance_name);
    option.per_instance = 1;
    option.name = instance_name;
    coverpoint var_name {
      bins range = {[lower:higher]}; 
    }
  endgroup
  
  initial begin
    check_addr c_low = new(addr, 0, 3, "low");
    check_addr c_mid = new(addr, 4, 11, "mid");
    check_addr c_hi  = new(addr, 12, 15, "high");
    
    for (int i = 0; i < 50; i++) begin
      addr = $urandom();
      c_low.sample();
      c_mid.sample();
      c_hi.sample();
    end
  end
endmodule

#     COVERGROUP COVERAGE
#     =============================================================
#     |        Covergroup         |   Hits   |  Goal /  | Status  |
#     |                           |          | At Least |         |
#     =============================================================
#     | TYPE /tb/check_addr       | 100.000% | 100.000% | Covered |
#     =============================================================
#     | INSTANCE low              | 100.000% | 100.000% | Covered |
#     |---------------------------|----------|----------|---------|
#     | COVERPOINT low::var_name  | 100.000% | 100.000% | Covered |
#     |---------------------------|----------|----------|---------|
#     | bin range                 |       14 |        1 | Covered |
#     =============================================================
#     | INSTANCE mid              | 100.000% | 100.000% | Covered |
#     |---------------------------|----------|----------|---------|
#     | COVERPOINT mid::var_name  | 100.000% | 100.000% | Covered |
#     |---------------------------|----------|----------|---------|
#     | bin range                 |       23 |        1 | Covered |
#     =============================================================
#     | INSTANCE high             | 100.000% | 100.000% | Covered |
#     |---------------------------|----------|----------|---------|
#     | COVERPOINT high::var_name | 100.000% | 100.000% | Covered |
#     |---------------------------|----------|----------|---------|
#     | bin range                 |       13 |        1 | Covered |
#     =============================================================
```
