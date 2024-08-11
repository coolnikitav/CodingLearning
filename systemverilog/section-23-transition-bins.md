# Transition Bins

## Simple Transition Coverage
- Q: Show an example of transition coverage.

```
module tb;
  reg clk = 0, din = 0, rst = 0;
  wire dout;
  
  
  fsm dut (clk, din, rst, dout);
  
  always #5 clk = ~clk;
  
  initial begin
    repeat(4) @(posedge clk) {rst,din} = 2'b10;
    repeat(4) @(posedge clk) {rst,din} = 2'b01;
    repeat(4) @(posedge clk) {rst,din} = 2'b10;
    repeat(4) @(posedge clk) {rst,din} = 2'b01;
    repeat(4) @(posedge clk) {rst,din} = 2'b00;
    		  @(posedge clk) {rst,din} = 2'b01;
    repeat(4) @(posedge clk) {rst,din} = 2'b00;
  end
  
  covergroup c1 @(posedge clk);
    option.per_instance = 1;
    coverpoint rst {
      bins rst_l = {0};
      bins rst_h = {1};
    }
    coverpoint din {
      bins din_h = {1};  
    }
    coverpoint dout {
      bins dout_l = {0};
      bins dout_h = {1};
    }
    coverpoint dut.state iff (din == 1'b1) {
      bins trans_s0_s1 = (dut.s0 => dut.s1);
      bins trans_s1_s0 = (dut.s1 => dut.s0);
      illegal_bins same_state = (dut.s0 => dut.s0, dut.s1 => dut.s1);
    }
    cross rst, din, dut.state {
      ignore_bins rst_high = binsof(rst) intersect {1}; 
    }
  endgroup
  ///////////////////////
  covergroup c2 @(posedge clk);
    option.per_instance = 1;
    coverpoint rst {
      bins rst_l = {0};
      bins rst_h = {1};
    }
    coverpoint din {
      bins din_l = {0}; 
    }
    coverpoint dut.state iff (din == 1'b0) {
      bins trans_s0_s0 = (dut.s0 => dut.s0);
      bins trans_s1_s1 = (dut.s1 => dut.s1);
      illegal_bins diff_state = (dut.s0 => dut.s1, dut.s1 => dut.s0);
    }
    cross rst, din, dut.state {
      ignore_bins rsl_high = binsof(rst) intersect {1}; 
    }
  endgroup
  
  initial begin
    c1 c_1 = new();
    c2 c_2 = new();
    #500;
    $finish();
  end
endmodule

#     COVERGROUP COVERAGE
#     =====================================================================
#     |            Covergroup            |   Hits   |  Goal /  |  Status  |
#     |                                  |          | At Least |          |
#     =====================================================================
#     | TYPE /tb/c1                      | 100.000% | 100.000% | Covered  |
#     =====================================================================
#     | INSTANCE <UNNAMED1>              | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::rst       | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin rst_l                        |       42 |        1 | Covered  |
#     | bin rst_h                        |        8 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::din       | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin din_h                        |        9 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::dout      | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin dout_l                       |       46 |        1 | Covered  |
#     | bin dout_h                       |        4 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::dut.state | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin trans_s0_s1                  |        4 |        1 | Covered  |
#     | bin trans_s1_s0                  |        4 |        1 | Covered  |
#     | illegal bin same_state           |        0 |    -     | Zero     |
#     |----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::\\2 \          | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin <rst_l,din_h,trans_s0_s1>    |        4 |        1 | Covered  |
#     | bin <rst_l,din_h,trans_s1_s0>    |        4 |        1 | Covered  |
#     =====================================================================
#     | TYPE /tb/c2                      | 100.000% | 100.000% | Covered  |
#     =====================================================================
#     | INSTANCE <UNNAMED1>              | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::rst       | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin rst_l                        |       42 |        1 | Covered  |
#     | bin rst_h                        |        8 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::din       | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin din_l                        |       41 |        1 | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::dut.state | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin trans_s0_s0                  |       12 |        1 | Covered  |
#     | bin trans_s1_s1                  |       27 |        1 | Covered  |
#     | illegal bin diff_state           |        0 |    -     | Zero     |
#     |----------------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::\\2 \          | 100.000% | 100.000% | Covered  |
#     |----------------------------------|----------|----------|----------|
#     | bin <rst_l,din_l,trans_s0_s0>    |        4 |        1 | Covered  |
#     | bin <rst_l,din_l,trans_s1_s1>    |       27 |        1 | Covered  |
#     | ignore bin rsl_high              |        8 |    -     | Occurred |
#     =====================================================================
```

## Consecutive Repetition Transition
```
module tb;
  reg clk = 0;
  reg data[] = {1,1,1,1,1,0,1,0,0};
  reg state = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    for (int i = 0; i < 9; i++) begin
      @(posedge clk);
      state = data[i];
    end
  end
  
  covergroup c @(posedge clk);
    option.per_instance = 1;
    coverpoint state {
      bins trans_0_1 = (1[*4]); // 4 consecutive ones
    }
  endgroup
  
  initial begin
    c ci = new();
    #100;
    $finish();
  end
endmodule

#     COVERGROUP COVERAGE
#     ================================================================
#     |          Covergroup          |   Hits   |  Goal /  | Status  |
#     |                              |          | At Least |         |
#     ================================================================
#     | TYPE /tb/c                   | 100.000% | 100.000% | Covered |
#     ================================================================
#     | INSTANCE <UNNAMED1>          | 100.000% | 100.000% | Covered |
#     |------------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::state | 100.000% | 100.000% | Covered |
#     |------------------------------|----------|----------|---------|
#     | bin trans_0_1                |        2 |        1 | Covered |
#     ================================================================
```
```
module tb;
  reg clk = 0;
  reg data[] = {1,1,1,1,0,1,1,1,1,0,1,0,0};
  reg state = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    for (int i = 0; i < 9; i++) begin
      @(posedge clk);
      state = data[i];
    end
  end
  
  covergroup c @(posedge clk);
    option.per_instance = 1;
    coverpoint state {
      bins trans_0_1 = (0=>1[*4]); // 4 consecutive ones that transitioned from zero
    }
  endgroup
  
  initial begin
    c ci = new();
    #100;
    $finish();
  end
endmodule

#     COVERGROUP COVERAGE
#     ================================================================
#     |          Covergroup          |   Hits   |  Goal /  | Status  |
#     |                              |          | At Least |         |
#     ================================================================
#     | TYPE /tb/c                   | 100.000% | 100.000% | Covered |
#     ================================================================
#     | INSTANCE <UNNAMED1>          | 100.000% | 100.000% | Covered |
#     |------------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::state | 100.000% | 100.000% | Covered |
#     |------------------------------|----------|----------|---------|
#     | bin trans_0_1                |        2 |        1 | Covered |
#     ================================================================
```

## Non-consecutive Transition
```
module tb;
  reg clk = 0;
  reg data[] = {0,0,0,1,1,0,0,1,0,1,0,1,1,1,0};
  reg state = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    for (int i = 0; i < 15; i++) begin
      @(posedge clk);
      state = data[i];
    end
  end
  
  covergroup c @(posedge clk);
    option.per_instance = 1;
    coverpoint state {
      bins trans_0_1 = (1[=5]);  // non-consecutive
    }
  endgroup
  
  initial begin
    c ci = new();
    #150;
    $finish();
  end
endmodule

#     COVERGROUP COVERAGE
#     ================================================================
#     |          Covergroup          |   Hits   |  Goal /  | Status  |
#     |                              |          | At Least |         |
#     ================================================================
#     | TYPE /tb/c                   | 100.000% | 100.000% | Covered |
#     ================================================================
#     | INSTANCE <UNNAMED1>          | 100.000% | 100.000% | Covered |
#     |------------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::state | 100.000% | 100.000% | Covered |
#     |------------------------------|----------|----------|---------|
#     | bin trans_0_1                |        3 |        1 | Covered |
#     ================================================================
```
```
covergroup c @(posedge clk);
    option.per_instance = 1;
    coverpoint state {
      bins trans_0_1 = (1[=5]);  // non-consecutive
    }
  endgroup
```
```
module tb;
  reg clk = 0;
  reg data[] = {0,0,0,1,1,0,0,1,0,1,0,1,1,1,0};
  reg state = 0;
  
  always #5 clk = ~clk;
  
  initial begin
    for (int i = 0; i < 15; i++) begin
      @(posedge clk);
      state = data[i];
    end
  end
  
  covergroup c @(posedge clk);
    option.per_instance = 1;
    coverpoint state {
      bins trans_0_1 = (0=>1[->5]=>0);  // non-consecutive
    }
  endgroup
  
  initial begin
    c ci = new();
    #250;
    $finish();
  end
endmodule

#     COVERGROUP COVERAGE
#     ================================================================
#     |          Covergroup          |   Hits   |  Goal /  | Status  |
#     |                              |          | At Least |         |
#     ================================================================
#     | TYPE /tb/c                   | 100.000% | 100.000% | Covered |
#     ================================================================
#     | INSTANCE <UNNAMED1>          | 100.000% | 100.000% | Covered |
#     |------------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::state | 100.000% | 100.000% | Covered |
#     |------------------------------|----------|----------|---------|
#     | bin trans_0_1                |        1 |        1 | Covered |
#     ================================================================
```

## Summary
- [*n] - consecutive
- [=n] - non-consecutive repetition
- [->n] - allows us to match an expression
