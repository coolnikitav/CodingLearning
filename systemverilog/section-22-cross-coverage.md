# Cross Coverage

## Understanding Cross Coverage
![image](https://github.com/user-attachments/assets/b15579c6-544d-4815-a641-a9b933957520)

![image](https://github.com/user-attachments/assets/0c4e026b-ef6f-4e31-9ab3-dec3c12b3b84)

![image](https://github.com/user-attachments/assets/af9b0a43-26aa-471d-b0b9-6c41242ea381)

```
module tb;
  reg wr;
  reg [1:0] addr;
  reg [3:0] din, dout;
  
  covergroup c;
    option.per_instance = 1;
    coverpoint wr {
      bins wr_low  = {0};
      bins wr_high = {1};
    }
    coverpoint addr {
      bins addr_v[] = {[0:3]}; 
    }
    cross wr, addr;
    coverpoint din {
      bins din_low  = {[0:3]};
      bins din_mid  = {[4:11]};
      bins din_high = {[12:15]};
    }
    coverpoint dout {
      bins dout_low  = {[0:3]};
      bins dout_mid  = {[4:11]};
      bins dout_high = {[12:15]};
    }
    cross wr, addr, din;
    cross wr, addr, dout;
  endgroup
  
  initial begin
    c ci = new();
    
    for (int i = 0; i < 50; i++) begin
      wr   = $urandom();
      addr = $urandom();
      din  = $urandom();
      ci.sample();
    end
  end
endmodule

#     COVERGROUP COVERAGE
#     ======================================================================
#     |            Covergroup            |   Hits   |  Goal /  |  Status   |
#     |                                  |          | At Least |           |
#     ======================================================================
#     | TYPE /tb/c                       |  69.047% | 100.000% | Uncovered |
#     ======================================================================
#     | INSTANCE <UNNAMED1>              |  69.047% | 100.000% | Uncovered |
#     |----------------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::wr        | 100.000% | 100.000% | Covered   |
#     |----------------------------------|----------|----------|-----------|
#     | bin wr_low                       |       22 |        1 | Covered   |
#     | bin wr_high                      |       28 |        1 | Covered   |
#     |----------------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::addr      | 100.000% | 100.000% | Covered   |
#     |----------------------------------|----------|----------|-----------|
#     | bin addr_v[0]                    |       16 |        1 | Covered   |
#     | bin addr_v[1]                    |        7 |        1 | Covered   |
#     | bin addr_v[2]                    |       14 |        1 | Covered   |
#     | bin addr_v[3]                    |       13 |        1 | Covered   |
#     |----------------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::din       | 100.000% | 100.000% | Covered   |
#     |----------------------------------|----------|----------|-----------|
#     | bin din_low                      |       17 |        1 | Covered   |
#     | bin din_mid                      |       21 |        1 | Covered   |
#     | bin din_high                     |       12 |        1 | Covered   |
#     |----------------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::dout      |   0.000% | 100.000% | Zero      |
#     |----------------------------------|----------|----------|-----------|
#     | bin dout_low                     |        0 |        1 | Zero      |
#     | bin dout_mid                     |        0 |        1 | Zero      |
#     | bin dout_high                    |        0 |        1 | Zero      |
#     |----------------------------------|----------|----------|-----------|
#     | CROSS <UNNAMED1>::\\1 \          | 100.000% | 100.000% | Covered   |
#     |----------------------------------|----------|----------|-----------|
#     | bin <wr_low,addr_v[0]>           |        6 |        1 | Covered   |
#     | bin <wr_low,addr_v[1]>           |        5 |        1 | Covered   |
#     | bin <wr_low,addr_v[2]>           |        5 |        1 | Covered   |
#     | bin <wr_low,addr_v[3]>           |        6 |        1 | Covered   |
#     | bin <wr_high,addr_v[0]>          |       10 |        1 | Covered   |
#     | bin <wr_high,addr_v[1]>          |        2 |        1 | Covered   |
#     | bin <wr_high,addr_v[2]>          |        9 |        1 | Covered   |
#     | bin <wr_high,addr_v[3]>          |        7 |        1 | Covered   |
#     |----------------------------------|----------|----------|-----------|
#     | CROSS <UNNAMED1>::\\2 \          |  83.333% | 100.000% | Uncovered |
#     |----------------------------------|----------|----------|-----------|
#     | bin <wr_low,addr_v[0],din_low>   |        3 |        1 | Covered   |
#     | bin <wr_low,addr_v[0],din_mid>   |        3 |        1 | Covered   |
#     | bin <wr_low,addr_v[1],din_low>   |        3 |        1 | Covered   |
#     | bin <wr_low,addr_v[1],din_mid>   |        2 |        1 | Covered   |
#     | bin <wr_low,addr_v[2],din_low>   |        2 |        1 | Covered   |
#     | bin <wr_low,addr_v[2],din_mid>   |        2 |        1 | Covered   |
#     | bin <wr_low,addr_v[2],din_high>  |        1 |        1 | Covered   |
#     | bin <wr_low,addr_v[3],din_low>   |        2 |        1 | Covered   |
#     | bin <wr_low,addr_v[3],din_mid>   |        3 |        1 | Covered   |
#     | bin <wr_low,addr_v[3],din_high>  |        1 |        1 | Covered   |
#     | bin <wr_high,addr_v[0],din_low>  |        2 |        1 | Covered   |
#     | bin <wr_high,addr_v[0],din_mid>  |        5 |        1 | Covered   |
#     | bin <wr_high,addr_v[0],din_high> |        3 |        1 | Covered   |
#     | bin <wr_high,addr_v[1],din_high> |        2 |        1 | Covered   |
#     | bin <wr_high,addr_v[2],din_low>  |        2 |        1 | Covered   |
#     | bin <wr_high,addr_v[2],din_mid>  |        4 |        1 | Covered   |
#     | bin <wr_high,addr_v[2],din_high> |        3 |        1 | Covered   |
#     | bin <wr_high,addr_v[3],din_low>  |        3 |        1 | Covered   |
#     | bin <wr_high,addr_v[3],din_mid>  |        2 |        1 | Covered   |
#     | bin <wr_high,addr_v[3],din_high> |        2 |        1 | Covered   |
#     |----------------------------------|----------|----------|-----------|
#     | CROSS <UNNAMED1>::\\3 \          |   0.000% | 100.000% | Zero      |
#     ======================================================================
```

## Filtering Combination Method 1: Creating Independent Covergroup
```
module tb;
  reg wr;
  reg [1:0] addr;
  reg [3:0] din, dout;
  
  covergroup c_wr_1;
    option.per_instance = 1;
    coverpoint wr {
      bins wr_high = {1}; 
    }
    coverpoint addr {
      bins addr_v[] = {0,1,2,3}; 
    }
    coverpoint din {
      bins low = {[0:3]};
      bins mid = {[4:11]};
      bins hig = {[12:15]};
    }
    cross wr, addr, din;
  endgroup
  
  covergroup c_wr_0;
    option.per_instance = 1;
    coverpoint wr {
      bins wr_low = {0}; 
    }
    coverpoint addr {
      bins addr_v[] = {0,1,2,3}; 
    }
    coverpoint dout {
      bins low = {[0:3]};
      bins mid = {[4:11]};
      bins hig = {[12:15]};
    }
    cross wr, addr, dout;
  endgroup
  
  initial begin
    c_wr_1 c1 = new();
    c_wr_0 c0 = new();
    
    for (int i = 0; i < 50; i++) begin
      wr   = $urandom();
      addr = $urandom();
      din  = $urandom();
      dout = $urandom();
      c1.sample();
      c0.sample();
    end
  end
endmodule

#     COVERGROUP COVERAGE
#     =================================================================
#     |         Covergroup          |   Hits   |  Goal /  |  Status   |
#     |                             |          | At Least |           |
#     =================================================================
#     | TYPE /tb/c_wr_1             |  93.750% | 100.000% | Uncovered |
#     =================================================================
#     | INSTANCE <UNNAMED1>         |  93.750% | 100.000% | Uncovered |
#     |-----------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::wr   | 100.000% | 100.000% | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | bin wr_high                 |       19 |        1 | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::addr | 100.000% | 100.000% | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | bin addr_v[0]               |       14 |        1 | Covered   |
#     | bin addr_v[1]               |       12 |        1 | Covered   |
#     | bin addr_v[2]               |       15 |        1 | Covered   |
#     | bin addr_v[3]               |        9 |        1 | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::din  | 100.000% | 100.000% | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | bin low                     |       16 |        1 | Covered   |
#     | bin mid                     |       20 |        1 | Covered   |
#     | bin hig                     |       14 |        1 | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | CROSS <UNNAMED1>::\\1 \     |  75.000% | 100.000% | Uncovered |
#     |-----------------------------|----------|----------|-----------|
#     | bin <wr_high,addr_v[0],low> |        1 |        1 | Covered   |
#     | bin <wr_high,addr_v[0],mid> |        4 |        1 | Covered   |
#     | bin <wr_high,addr_v[0],hig> |        1 |        1 | Covered   |
#     | bin <wr_high,addr_v[1],low> |        2 |        1 | Covered   |
#     | bin <wr_high,addr_v[1],mid> |        2 |        1 | Covered   |
#     | bin <wr_high,addr_v[1],hig> |        3 |        1 | Covered   |
#     | bin <wr_high,addr_v[2],mid> |        4 |        1 | Covered   |
#     | bin <wr_high,addr_v[2],hig> |        1 |        1 | Covered   |
#     | bin <wr_high,addr_v[3],mid> |        1 |        1 | Covered   |
#     =================================================================
#     | TYPE /tb/c_wr_0             |  95.833% | 100.000% | Uncovered |
#     =================================================================
#     | INSTANCE <UNNAMED1>         |  95.833% | 100.000% | Uncovered |
#     |-----------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::wr   | 100.000% | 100.000% | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | bin wr_low                  |       31 |        1 | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::addr | 100.000% | 100.000% | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | bin addr_v[0]               |       14 |        1 | Covered   |
#     | bin addr_v[1]               |       12 |        1 | Covered   |
#     | bin addr_v[2]               |       15 |        1 | Covered   |
#     | bin addr_v[3]               |        9 |        1 | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::dout | 100.000% | 100.000% | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | bin low                     |       13 |        1 | Covered   |
#     | bin mid                     |       23 |        1 | Covered   |
#     | bin hig                     |       14 |        1 | Covered   |
#     |-----------------------------|----------|----------|-----------|
#     | CROSS <UNNAMED1>::\\1 \     |  83.333% | 100.000% | Uncovered |
#     |-----------------------------|----------|----------|-----------|
#     | bin <wr_low,addr_v[0],low>  |        3 |        1 | Covered   |
#     | bin <wr_low,addr_v[0],mid>  |        4 |        1 | Covered   |
#     | bin <wr_low,addr_v[0],hig>  |        1 |        1 | Covered   |
#     | bin <wr_low,addr_v[1],hig>  |        5 |        1 | Covered   |
#     | bin <wr_low,addr_v[2],low>  |        4 |        1 | Covered   |
#     | bin <wr_low,addr_v[2],mid>  |        5 |        1 | Covered   |
#     | bin <wr_low,addr_v[2],hig>  |        1 |        1 | Covered   |
#     | bin <wr_low,addr_v[3],low>  |        2 |        1 | Covered   |
#     | bin <wr_low,addr_v[3],mid>  |        4 |        1 | Covered   |
#     | bin <wr_low,addr_v[3],hig>  |        2 |        1 | Covered   |
#     =================================================================
```

## Filtering Combination Method 2: binsof(SIG) intersec {VAL}
```
module tb;
 
  reg wr;
  reg [1:0] addr;
  reg [3:0] din , dout;
  
  integer i = 0;
 
 
 covergroup c ;
   
    option.per_instance = 1;
   
    coverpoint wr {
      bins wr_low = {0};
      bins wr_high = {1};
    }
   
   coverpoint  addr {
    
     bins addr_v[] = {0,1,2,3}; 
   
   }
   
  
   ///////////////////////////////
    
   coverpoint din { //wr = 1
    
      bins low = {[0:3]};
      bins mid = {[4:11]};
      bins hig = {[12:15]};
    }
   
   coverpoint dout { /// wr = 0
    
      bins low = {[0:3]};
      bins mid = {[4:11]};
      bins hig = {[12:15]};
    }
  
   ////////////////write operation
   cross wr,addr, din
   {
    ignore_bins wr_low_unused = binsof (wr) intersect {0};
   }
   
   //////////////read operation
   cross wr,addr, dout
   {
     ignore_bins wr_high_unused = binsof (wr) intersect {1}; 
   }
 
    
  endgroup
  
  ///////////////////ignore bins to remove from coverage calc
  //////////// bins to include coverage in computation
  
 
  c ci;
 
  initial begin
    ci = new();
    
    
    
    for (i = 0; i <100; i++) begin
      addr = $urandom();
      wr = $urandom();
      din = $urandom();
      dout = $urandom();
      ci.sample();
      #10;
    end
    
    
  end
  
  
  
  
  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;
    #1000;
    $finish();
  end
  
 
 
 
 
endmodule

#     COVERGROUP COVERAGE
#     ================================================================
#     |         Covergroup          |   Hits   |  Goal /  |  Status  |
#     |                             |          | At Least |          |
#     ================================================================
#     | TYPE /tb/c                  | 100.000% | 100.000% | Covered  |
#     ================================================================
#     | INSTANCE <UNNAMED1>         | 100.000% | 100.000% | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::wr   | 100.000% | 100.000% | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | bin wr_low                  |       54 |        1 | Covered  |
#     | bin wr_high                 |       46 |        1 | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::addr | 100.000% | 100.000% | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | bin addr_v[0]               |       28 |        1 | Covered  |
#     | bin addr_v[1]               |       25 |        1 | Covered  |
#     | bin addr_v[2]               |       30 |        1 | Covered  |
#     | bin addr_v[3]               |       17 |        1 | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::din  | 100.000% | 100.000% | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | bin low                     |       30 |        1 | Covered  |
#     | bin mid                     |       46 |        1 | Covered  |
#     | bin hig                     |       24 |        1 | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | COVERPOINT <UNNAMED1>::dout | 100.000% | 100.000% | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | bin low                     |       21 |        1 | Covered  |
#     | bin mid                     |       50 |        1 | Covered  |
#     | bin hig                     |       29 |        1 | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::\\1 \     | 100.000% | 100.000% | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | bin <wr_high,addr_v[0],low> |        5 |        1 | Covered  |
#     | bin <wr_high,addr_v[0],mid> |        3 |        1 | Covered  |
#     | bin <wr_high,addr_v[0],hig> |        7 |        1 | Covered  |
#     | bin <wr_high,addr_v[1],low> |        1 |        1 | Covered  |
#     | bin <wr_high,addr_v[1],mid> |        4 |        1 | Covered  |
#     | bin <wr_high,addr_v[1],hig> |        3 |        1 | Covered  |
#     | bin <wr_high,addr_v[2],low> |        3 |        1 | Covered  |
#     | bin <wr_high,addr_v[2],mid> |        8 |        1 | Covered  |
#     | bin <wr_high,addr_v[2],hig> |        1 |        1 | Covered  |
#     | bin <wr_high,addr_v[3],low> |        2 |        1 | Covered  |
#     | bin <wr_high,addr_v[3],mid> |        8 |        1 | Covered  |
#     | bin <wr_high,addr_v[3],hig> |        1 |        1 | Covered  |
#     | ignore bin wr_low_unused    |       54 |    -     | Occurred |
#     |-----------------------------|----------|----------|----------|
#     | CROSS <UNNAMED1>::\\2 \     | 100.000% | 100.000% | Covered  |
#     |-----------------------------|----------|----------|----------|
#     | bin <wr_low,addr_v[0],low>  |        3 |        1 | Covered  |
#     | bin <wr_low,addr_v[0],mid>  |        9 |        1 | Covered  |
#     | bin <wr_low,addr_v[0],hig>  |        1 |        1 | Covered  |
#     | bin <wr_low,addr_v[1],low>  |        5 |        1 | Covered  |
#     | bin <wr_low,addr_v[1],mid>  |        7 |        1 | Covered  |
#     | bin <wr_low,addr_v[1],hig>  |        5 |        1 | Covered  |
#     | bin <wr_low,addr_v[2],low>  |        6 |        1 | Covered  |
#     | bin <wr_low,addr_v[2],mid>  |        9 |        1 | Covered  |
#     | bin <wr_low,addr_v[2],hig>  |        3 |        1 | Covered  |
#     | bin <wr_low,addr_v[3],low>  |        1 |        1 | Covered  |
#     | bin <wr_low,addr_v[3],mid>  |        4 |        1 | Covered  |
#     | bin <wr_low,addr_v[3],hig>  |        1 |        1 | Covered  |
#     | ignore bin wr_high_unused   |       46 |    -     | Occurred |
#     ================================================================
```

```
module tb;
 
  reg [2:0] din;
  reg wr;
  int i = 0;
  
   covergroup c ;
   
    option.per_instance = 1;
   
     coverpoint wr
     {
      bins wr_l = {0};
      bins wr_h = {1};
     }
     
     coverpoint din;
     
   //  cross wr, din;
     
     cross wr,din
     {
     
       ignore_bins unused_din = binsof(din) intersect {[5:7]}; 
       ignore_bins unused_wr  = binsof(wr) intersect {0};
     }
     
  
  endgroup
  
  ///////////////////ignore bins to remove from coverage calc
  //////////// bins to include coverage in computation
  
 
  c ci;
 
  initial begin
    ci = new();
    
    
    
    for (i = 0; i <10; i++) begin
      din = $urandom();
      wr = $urandom();
      ci.sample();
      $display("wr : %d din : %0d", wr,din);
      #10;
    end
    
    
  end
  
  
  
  
  initial begin
    $dumpfile("dump.vcd"); 
    $dumpvars;
    #1000;
    $finish();
  end
  
 
 
 
 
endmodule
```

![image](https://github.com/user-attachments/assets/8f546f94-27c8-49fc-a6bd-f90e6e833a33)
