# Working With Multiple Sequences

## Fundamentals of Boolean Operators
boolean operators
- and
- or
- not

```
sequence s1;
  a[*1];
endsequence

sequence s2;
  b[*2];
endsequence

assert (@(posedg clk) $rose(start) |-> s1 and s2);
```

## Usage of AND Operator
If start is asserted, both a and b should remain high for 2 consecutive clock ticks. b will become high in the next clock tickk after a becomes high
