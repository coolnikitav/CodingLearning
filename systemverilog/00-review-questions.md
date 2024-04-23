## Set 1
4 - What is inheritance?

Child class inheriting or having access to members and have the capability of performing functions of the parent class.

3 - How do you implement randc in SystemVerilog?

randc generates a random int that hasn't been generated yet.
```
class a;
  randc bit a;
endclass

class generator;
  a = new();
  a.randomize();
endclass
```
2 - What is the use of scope resolution operator?

:: allows to access members of a class.

1 - How will you test the functionality of interrupts using functional coverage?

I define the types of interrupts I want to test. Then randomize those types and apply the stimulus to the dut. Then I would collect the results and compare with expected.
