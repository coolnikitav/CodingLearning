# Common Examples

## Boolean Operator
- Both a and b must be high
```
assert property(@(posedge clk) a && b);
```
- Either of one a or b could be high
```
assert property(@(posedge clk) a || b);
```
- One of the signals is high while other must be low
```
assert property(@(posegde clk) a ^ b);
```
- Both signals must be low
```
assert property (@(posedge clk) !a && !b);
```

## Implication Operator
- If antecedent is high then consequent must be high on the same clock cycle
```
assert property (@(posedge clk) a |-> b);
```
- If antecedent is high then consequent must be low on the same clock cycle
```
assert property (@(posedge clk) a |-> !b);
```

## Delay Operator
- a must be high after 2 clock cycles initially
```
initial assert property (@(posedge clk) ##2 a);
```
- If a assert, it must remain high for two clock ticks
```
assert property (@(posedge clk) $rose(a) |-> a[*2]);
```
- If a assert, b should assert after 4 clock cycles
```
assert property (@(posedge clk) $rose(a) |-> ##4 $rose(b));
```
- a followed by b followed by c
```
assert property (@(posedge clk) a ## b ## c);
```

## Delay Operator with Range
- rst should become low within 4 to 5 clock cycles
```
initial assert property (@(posedge clk) ##[4:5] !rst);
```
- If rst deassert then ce must assert within 2 to 3 clock cycles
```
assert property (@(posedge clk) $fell(rst) |-> ##[2:3] $rose(ce));
```
- ack should be granted/given to the new req within 0 to 1 clock cycles
```
assert property (@(posedge clk) $rose(req) |-> ##[0:1] ack);
```

## Unbounded Delay
- If a assert, b must assert at same clock cycle or anytime later durig simulation
```
assert property (@(posedge clk) $rose(a) |-> s_eventually $rose(b));
```
- If a assert, b deassert in the next clock cycle or somewhere during simulation
```
assert property (@(posedge clk) $rose(a) |=> s_eventually $fell(b));
```
- rst must become low somewhere during simulation
```
initial assert property (@(posedge clk) s_eventually $fell(rst));
```
- b must become high anytime later during simulation
```
initial assert property (@(posedge clk) s_eventually b));
```

## Repetition Operator
- If rd assert then it must stay high for 2 clock cycles
```
assert property (@(posedge clk) $rose(rst) |-> rst[*2]);
```
- 3 consecutive wr should be followed by 2 rd requests
```
assert property (@(posedge clk) wr[*3] |=> rd[*2]);
```
- If rst deassert, ce must remain high
```
assert property (@(posedge clk) $fell(rst) |-> ce[*1:$]);
```
