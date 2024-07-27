# Getting Started With Bins

## Fundamentals of Implicit/automatic bins
![image](https://github.com/user-attachments/assets/32711f32-940e-4f2c-a830-3393a9b34234)

![image](https://github.com/user-attachments/assets/5c76979e-6081-4a1e-895f-e745193b6c52)

![image](https://github.com/user-attachments/assets/a0b43965-2976-4da4-b26d-842d9386228e)

## Explicit bins
- Q: How to specify the bins to a single number? What about a range? How to use the array?
  
Implicit bins are created by the simulator and it tries to divide them evenly.

```
covergroup cvr_a;
  option.per_instance = 1;
  coverpoint a {
    bins zero = {0};
    bins one = {1};
    bins two = {2};
    bins three = {3};
  }
endgroup
```
```
covergroup cvr_a;
  option.per_instance = 1;
  coverpoint a {
    bins bin0 = {[0:1]};
    bins bin1 = {[2:3]};
  }
endgroup
```
```
covergroup cvr_a;
  option.per_instance = 1;
  coverpoint a {
    bins bina[] = {0,1,2,3};
  }
endgroup

#     COVERGROUP COVERAGE
#     ============================================================
#     |        Covergroup        |   Hits   |  Goal /  | Status  |
#     |                          |          | At Least |         |
#     ============================================================
#     | TYPE /tb/cvr_a           | 100.000% | 100.000% | Covered |
#     ============================================================
#     | INSTANCE <UNNAMED1>      | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | COVERPOINT <UNNAMED1>::a | 100.000% | 100.000% | Covered |
#     |--------------------------|----------|----------|---------|
#     | bin bina[0]              |        4 |        1 | Covered |
#     | bin bina[1]              |        5 |        1 | Covered |
#     | bin bina[2]              |        7 |        1 | Covered |
#     | bin bina[3]              |        4 |        1 | Covered |
#     ============================================================
```
```
reg [6:0] a;
  
covergroup cvr_a;
  option.per_instance = 1;
  coverpoint a {
    bins bina[] = {[0:127]};
  }
endgroup
```
```
covergroup cvr_a;
  option.per_instance = 1;
  coverpoint a {
    bins bina[64] = {[0:127]};  // each bin keeps track on 2 values
  }
endgroup
```
![image](https://github.com/user-attachments/assets/e396d66e-351d-4611-a659-d99ef3fb18a7)

## Default
- Q: What are default bins and how are they used?

```
covergroup cvr_a;
  option.per_instance = 1;
  coverpoint a {
    bins a_values[] = {[0:9]};
    bins a_unused = default;
  }
endgroup

#     COVERGROUP COVERAGE
#     =============================================================
#     |        Covergroup        |  Hits   |  Goal /  |  Status   |
#     |                          |         | At Least |           |
#     =============================================================
#     | TYPE /tb/cvr_a           | 80.000% | 100.000% | Uncovered |
#     =============================================================
#     | INSTANCE <UNNAMED1>      | 80.000% | 100.000% | Uncovered |
#     |--------------------------|---------|----------|-----------|
#     | COVERPOINT <UNNAMED1>::a | 80.000% | 100.000% | Uncovered |
#     |--------------------------|---------|----------|-----------|
#     | bin a_values[0]          |       1 |        1 | Covered   |
#     | bin a_values[1]          |       1 |        1 | Covered   |
#     | bin a_values[2]          |       2 |        1 | Covered   |
#     | bin a_values[3]          |       2 |        1 | Covered   |
#     | bin a_values[4]          |       1 |        1 | Covered   |
#     | bin a_values[5]          |       0 |        1 | Zero      |
#     | bin a_values[6]          |       1 |        1 | Covered   |
#     | bin a_values[7]          |       2 |        1 | Covered   |
#     | bin a_values[8]          |       1 |        1 | Covered   |
#     | bin a_values[9]          |       0 |        1 | Zero      |
#     | default bin a_unused     |       9 |    -     | Occurred  |
#     =============================================================
```

## Types of Bins Summary
![image](https://github.com/user-attachments/assets/ec7da733-f771-4122-ae0e-4121ceda0bc5)

## Working with enum
- Q: Write the declaration for an enum.

```
module tb;
  typedef enum bit [1:0] {s0, s1, s2, s3} fsm_state;
  fsm_state var1;
  
  covergroup cvr_var1;
    option.per_instance = 1;
    coverpoint var1;
  endgroup
  
  initial begin
    cvr_var1 cia = new();
    for(int i = 0; i < 10; i++) begin
      var1 = s2;
      cia.sample();
    end
    
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #200;
    $finish();
  end
endmodule
```

## Working With a Simple FSM in Verilog
- Q: Write design code for this FSM:
- ![image](https://github.com/user-attachments/assets/ec5cad54-31ff-4bf6-a3b0-823761b9d4c1)
- Then write a testbench that shows state coverage. Make the testbench run like this:
```
  initial begin
    rst = 1;
    #30;
    rst = 0;
    #40;
    din = 1;
  end
```

```
module fsm(
  input      clk,
  input      rst,
  input      din,
  output reg dout
);
  reg state, next_state;
  
  parameter s0=0, s1=1;  // verilog uses parameter for this
  
  always @ (posedge clk or posedge rst)
    if (rst)
      state <= s0;
  	else
      state <= next_state;
  
  always @ (state or din) begin
    case (state)
      s0: begin
        if (din) begin
          dout = 1;
          next_state = s1;
        end else begin
          dout = 0;
          next_state = s0;
        end
      end
      s1: begin
        if (din) begin
          dout = 1;
          next_state = s0;
        end else begin
          dout = 0;
          next_state = s1;
        end
      end
      default: begin
        dout = 0;
        next_state = s0;
      end
    endcase
  end
endmodule
```
```
module tb;
  reg clk = 0;
  reg rst = 0;
  reg din = 0;
  wire dout;
  
  covergroup cvr_state;
    option.per_instance = 1;
    coverpoint dut.state;
  endgroup
  
  fsm dut (.clk(clk), .rst(rst), .din(din), .dout(dout));
  
  always #5 clk = ~clk;
  
  initial begin
    rst = 1;
    #30;
    rst = 0;
    #40;
    din = 1;
  end
  
  cvr_state ci;
  
  initial begin
    ci = new();
    forever begin
      @(posedge clk);
      ci.sample();
    end
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #200;
    $finish();
  end
endmodule
```
## Working with Simple FSM in SystemVerilog
- Q: How are states declared in SystemVerilog compared to Verilog?

```
module state_mach(
input rst,clk,
input din,
output logic dout
);
 
typedef enum {s0,s1} state_type;
state_type state = s0;
state_type next_state = s0;
 
/////////////Reset Logic
always_ff @(posedge clk) begin
	if(rst == 1'b1)
		state <= s0;
	else
		state <= next_state;
	end
 
///////////////Next state Decoder Logic
always_comb begin
	case(state)
		s0: begin
			if(din == 1'b1)
				next_state = s1;
			else
				next_state = s0;
			end 
		s1: begin
			if(din == 1'b1)
				next_state = s0;
			else
				next_state = s1;
			end 
		default : next_state = s0;
	endcase
end
 
///////////////Output Logic
 
always_comb begin
	case(state)
		s0: dout = 1'b0;
		s1: dout = 1'b1;
		default : dout = 1'b0;
	endcase
end
endmodule

```
