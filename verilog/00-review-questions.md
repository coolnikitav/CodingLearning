## Set 2
10 - What are parallel threads in Verilog?

I am not sure. My best guess is various parts of the program executing simultaneously is different threads. Or diffent programs simultaneously executing in different threads.

9 - What are different types of delay control?

Regular control: #50;

I don't really know other delay controls.

8 - What is verilog $random?

$random generates a random 32-bit unsigned integer in verilog.

7 - What is duty cycle?

Duty cycle is the percentage of time a digital signal stays on during 1 clock cycle.

6 - What do you understand by casex and casez statements in Verilog?

casex and casez are case statements or structures. In regular case the operand needs to match completely. In casex and casez, the digits of the operand that do not need to match completely are replaced by x and z, respectively. For example: if case is 4'b01x0, the 2nd MSB doesnt need to match.

5 - How can you generate a sine wave using the verilog coding style?

By using $sin(x) function.

4 - What is the difference between $setup and $hold?

They are constraints in the simulation. Setup time is the time signal has to be stable before it is read and hold time is time that signal has to be stable after it is read.

3 - Can 'define be used for text substitution through variable instead of literal substitution?

Yes, 'define can have a function defined in it.

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
