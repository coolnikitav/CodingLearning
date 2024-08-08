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
