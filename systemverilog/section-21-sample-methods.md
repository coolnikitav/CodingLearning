# Sample Methods

## Fundamentals
- Q: What are the 3 ways of sampling?

![image](https://github.com/user-attachments/assets/8599c3b5-0678-42cc-9708-1c78c5d2c1fd)

## Method 1: Sampling Event with covergroup
```
module tb;
  reg [1:0] a = 0;
  reg en = 0;
  reg clk = 0;
  
  always #5 clk = ~clk;
  
  always #10 en = ~en;
  
  covergroup c @(posedge clk);
    option.per_instance = 1;
    coverpoint a;
  endgroup
  
  /*
  covergroup c @(posedge en);
    option.per_instance = 1;
    coverpoint a;
  endgroup
  */
  
  initial begin
    c ci = new();
    
    for (int i = 0; i < 50; i++) begin
      @(posedge clk);
      a = $urandom();
    end
  end
  
  initial begin
    #500;
    $finish();
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
#     | COVERPOINT <UNNAMED1>::a | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | bin auto[0]              |   124933 |        1 | Covered |
#     | bin auto[1]              |   125060 |        1 | Covered |
#     | bin auto[2]              |   124962 |        1 | Covered |
#     | bin auto[3]              |   125045 |        1 | Covered |
#     ============================================================
```

## Method 2: Using Pre-Build sample() method

## User Defined Sample Method inside task block
```
module tb;
  reg [3:0] addr;
  reg wr;
  reg clk = 0;
  
  always #5 clk = ~clk;
  
  covergroup c with function sample(reg [3:0] in);
    option.per_instance = 1;
  	coverpoint in;  
  endgroup
  
  task write(c cvr);
    @(posedge clk);
    wr = 1;
    addr = $urandom();
    cvr.sample(addr);
  endtask
  
  initial begin
    c ci = new();
    
    for (int i = 0; i < 50; i++) begin
      write(ci);
    end
  end
  
  initial begin
    #500;
    $finish();
  end
endmodule

#     COVERGROUP COVERAGE
#     ==============================================================
#     |        Covergroup         |  Hits   |  Goal /  |  Status   |
#     |                           |         | At Least |           |
#     ==============================================================
#     | TYPE /tb/c                | 93.750% | 100.000% | Uncovered |
#     ==============================================================
#     | INSTANCE <UNNAMED1>       | 93.750% | 100.000% | Uncovered |
#     |---------------------------|---------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::in | 93.750% | 100.000% | Uncovered |
#     |---------------------------|---------|----------|-----------|
#     | bin auto[0]               |       6 |        1 | Covered   |
#     | bin auto[1]               |       7 |        1 | Covered   |
#     | bin auto[2]               |       3 |        1 | Covered   |
#     | bin auto[3]               |       3 |        1 | Covered   |
#     | bin auto[4]               |       4 |        1 | Covered   |
#     | bin auto[5]               |       1 |        1 | Covered   |
#     | bin auto[6]               |       3 |        1 | Covered   |
#     | bin auto[7]               |       2 |        1 | Covered   |
#     | bin auto[8]               |       0 |        1 | Zero      |
#     | bin auto[9]               |       4 |        1 | Covered   |
#     | bin auto[10]              |       2 |        1 | Covered   |
#     | bin auto[11]              |       3 |        1 | Covered   |
#     | bin auto[12]              |       5 |        1 | Covered   |
#     | bin auto[13]              |       1 |        1 | Covered   |
#     | bin auto[14]              |       2 |        1 | Covered   |
#     | bin auto[15]              |       4 |        1 | Covered   |
#     ==============================================================
```

## User Defined Sample Metod inside Function Block
```
module tb;
  reg rd, wr, en;
  reg [1:0] din;
  
  typedef enum {write, read, NOP, error} opstate;
  opstate o1, o2;
                                        
  function opstate detect_state (input rd, wr, en);
    if (en == 0)
      return NOP;
    else if (en == 1 && wr ==1  && rd == 0)
      return write;
    else if (en == 1 && rd == 1 && wr == 0)
      return read;
    else
      return error;
  endfunction
  
  function bit [1:0] decode_state (input opstate oin);
    if (oin == NOP)
      return 2'b00;
    else if (oin == write)
      return 2'b01;
    else if (oin == read)
      return 2'b10;
    else if (oin == error)
      return 2'b11;
  endfunction
  
  function check_cover (input rd, wr, en);  // we cannot pass in the covergroup because it technically changes it and causes a side effect
    o1 = detect_state(rd,wr,en);
    din = decode_state(o1);
    ci.sample(o1);
  endfunction
  
  covergroup c with function sample (input opstate cin);
    option.per_instance = 1;
    coverpoint cin;
  endgroup
  
  c ci;
  
  initial begin
    ci = new();
    
    for (int i = 0; i < 50; i++) begin
      wr = $urandom();
      rd = $urandom();
      en = $urandom();
      check_cover(rd, wr, en);
    end
  end
endmodule

#     COVERGROUP COVERAGE
#     ==============================================================
#     |         Covergroup         |   Hits   |  Goal /  | Status  |
#     |                            |          | At Least |         |
#     ==============================================================
#     | TYPE /tb/c                 | 100.000% | 100.000% | Covered |
#     ==============================================================
#     | INSTANCE <UNNAMED1>        | 100.000% | 100.000% | Covered |
#     |----------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::cin | 100.000% | 100.000% | Covered |
#     |----------------------------|----------|----------|---------|
#     | bin auto[write]            |        9 |        1 | Covered |
#     | bin auto[read]             |        4 |        1 | Covered |
#     | bin auto[NOP]              |       26 |        1 | Covered |
#     | bin auto[error]            |       11 |        1 | Covered |
#     ==============================================================
```

## User Defined Sample Method Inside Property Block
```
module tb;
  reg rd = 0, wr = 0;
  reg clk = 0;
  reg [4:0] addr;
  reg [7:0] din, dout;
  
  always #5 clk = ~clk;
  
  covergroup c with function sample (reg [4:0] addrin);
    option.per_instance = 1;
    coverpoint addrin {
      bins lower = {[0:7]};
      bins mid   = {[15:20]};
      bins high  = {[27:31]};
    }
  endgroup
  
  c ci;
  
  initial begin
    ci = new();
    @(posedge clk);
    addr = 3;
    wr   = 1;
    rd   = 0;
    @(posedge clk);
    addr = 3;
    wr   = 0;
    rd   = 1;
    dout = 12;
    @(posedge clk);
    addr = 17;
    wr   = 1;
    rd   = 0;
    din  = 21;
    @(posedge clk);
    addr = 17;
    wr   = 1;
    rd   = 0;
    dout = 21;
    @(posedge clk);
    addr = 28;
    wr   = 1;
    rd   = 0;
    din  = 67;
    @(posedge clk);
    addr = 28;
    wr   = 0;
    rd   = 1;
    dout = 67;
  end
  
  property p1;
    bit [4:0] addrs;
    bit [7:0] dvar;
    
    @(posedge clk) (wr |-> (wr, addrs = addr, dvar = din, ci.sample(addrs)) ##[1:50] rd[*1:50] ##0 (addrs == addr) ##0 (dout == dvar) );
  endproperty
  
  A1: assert property (p1) $info("Success at %0t", $time);
    
  initial begin
    $assertvacuousoff(0);
    #500;
    $finish();
  end
endmodule

# KERNEL: Info: testbench.sv (60): Success at 65

#     COVERGROUP COVERAGE
#     =================================================================
#     |          Covergroup           |   Hits   |  Goal /  | Status  |
#     |                               |          | At Least |         |
#     =================================================================
#     | TYPE /tb/c                    | 100.000% | 100.000% | Covered |
#     =================================================================
#     | INSTANCE <UNNAMED1>           | 100.000% | 100.000% | Covered |
#     |-------------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::addrin | 100.000% | 100.000% | Covered |
#     |-------------------------------|----------|----------|---------|
#     | bin lower                     |        1 |        1 | Covered |
#     | bin mid                       |        2 |        1 | Covered |
#     | bin high                      |        1 |        1 | Covered |
#     =================================================================
```
