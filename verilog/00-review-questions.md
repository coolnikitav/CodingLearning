## Set 3
10 - Give major differences between a task and a function.

Task is used to perform a series of actions. Function is used to process an input and get an output.

Function can accept multiple inputs and has one output. Task can have multiple outputs.

9 - What are blocking and non-blocking statements?

Blocking statements execute in sequence and use "="

Non-blocking statements execute in parallel and use "<="

8 - What is a reg in Verilog?

Reg is a variable that stores a value.

7 - What does a wire refer to?

Wire refers to a physical wire constantly connecting 2 nodes in a design.

6 - What are verilog parallel case and full case statements?

parallel case - a case statement where not every case it covered. In situations where case isn't covered, default behavior (latch) will be assumed.

full case - every possibility of a case is covered.

5 - Give a few examples of compiler directives.

`define - macros

`include - to include all of the content from another file into this one

`timescale - defines the timescale of the simulation

`ifdef ... endif - conditional statements

4 - What is meant by logic synthesis?

Logic getting synthesized into hardware layout.

3 - How is rise, fall and turnoff delays represented in Verilog?

It can be specified as one delay (equal delay for all 3), two delay (rise, fall), or three delay (rise, fall, turnoff).

One delay: #(5) | Two delay: #(5,6) | Three delay: #(6,7,8)

2 - What is $time in Verilog?

$time variable gives the current time of the simulation. By current time, meaning how long the simulation has been running.

1 - What is a defparam used for?

I am not sure. The name is default parameter. Maybe you could have a default paremeter as one of the function arguments if the argument is not specified.

## Set 2
10 - What are parallel threads in Verilog?

Multiple blocks within a module that execute concurrently. Parallel threads are also created in fork...join.

9 - What are different types of delay control?

#delay, @posedge, @negedge, wait

I don't really know other delay controls.

8 - What is verilog $random?

$random generates a random 32-bit signed integer in verilog.

7 - What is duty cycle?

Duty cycle is the percentage of time a digital signal stays on during 1 clock cycle.

6 - What do you understand by casex and casez statements in Verilog?

casex and casez are case statements or structures. In regular case the operand needs to match completely. In casex and casez, the digits of the operand that do not need to match completely are replaced by x/z/? and ?/Z, respectively. For example: if case is 4'b01x0, the 2nd MSB doesnt need to match.

5 - How can you generate a sine wave using the verilog coding style?

By using $sin(x) function.

4 - What is the difference between $setup and $hold?

They are constraints in the simulation. Setup time is the time signal has to be stable before it is read and hold time is time that signal has to be stable after it is read.

3 - Can 'define be used for text substitution through variable instead of literal substitution?

No. It can only be used for literal substitution with a value.

2 - What do you understand by continuous assignment?

I imagine a wire connected between 2 signals. The value of the output constantly reflects the value of the input.

1 - What are HDL simulators?

Hardware description language simulators compile our HDL code into a physical RTL layout and allow us to run a simulation to verify it.

## Set 1
1 - Write Verilog code to swap contents of two registers with and without a temporary register

```
// With temp
reg a,b,temp;

always @ (*) begin
  temp = a;
  a = b;
  b = temp;
end

// Without temp
reg a,b;

always @ (*) begin
  a <= b;
  b <= a;
end
```

2 - Elaborate on the file operation support in Verilog
I haven't specifically studied file operation in Verilog. However, I would assume you can read file, write to them.

3 - Difference between inter statement and intra statement delay?
Inter statement delay is the delay between statemenets. Intra statement delay is delay within a statement between its operations.

4 - What is delta simulation time?
It is used to model zero delay. It is the smallest delay that can be specified. It represents one step in the simulation. Usually used for combinatorial logic.

5 - What is meant by inferring latches and how can you avoid it?
A latch is inferred when not all logical posibilies are covered. You can avoid it by adding a default case that covers everything not explicitely stated.

6 - Which will be updated first - variables or signals?
Signals are updated first. They are wires and registers. Then variables are updated based on values of signals.

7 - Why is it necessary to list all inputs in the sensitivity ist of a combinational circuit?
So the output changes wheneve any of the inputs change.

8 - What are the main differences between VHDL and verilog?
VHDL is not case sensitive. It has 2 parts: architecture and entity. Verilog is made of modules. VHDL signals have 9 values, the same signals in Verilog have 4.

9 - Give some examples of commonly used Verilog system tasks and their purposes.
$display - print to the console during simulation

$random - generate a random 32 bit int

$finish - simulation termination

$fopen, $fclose - open and close a file

10 - Write a Verilog code for synchronous and asynchronous reset.

Synch:
```
always @ (posedge clk)
  if (reset)
    do reset;
```

Asynch:
```
always @ (posedge clk or posedge reset)
  if (reset)
    do reset;
```
