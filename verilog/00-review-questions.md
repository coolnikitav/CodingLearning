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
No difference. Example:
```
a = b; #5;
b=c;

a=b;
#5;
b=c;
```

4 - What is delta simulation time?
Size of the simulation step. For example, if timescale is 1ns/1ps, then delta is 1ns because that is the simulation step.

5 - What is meant by inferring latches and how can you avoid it?
A latch is inferred when not all logical posibilies are covered. You can avoid it by adding a default case that covers everything not explicitely stated.
