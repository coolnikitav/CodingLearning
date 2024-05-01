## Set 1
10 - Difference between dynamic and associative array.

Dynamic arrays are arrays defined without a size and can have size specified at runtime and then changed. Values are accessed using the index.

Associative arrays is a dictionary or a map. It's a collection of key-value pairs. Values are accessed using the key.

9 - Difference between module and program block?

Module contains RTL design code. A program is a verification container used to avoid race conditions by executing its contents at the end of the time step. It executes it in the reactive region, after the variables are updated.

8 - Difference between static and automatic variables.

A static variable gets initialized before time 0 at some memory location and stays there for the duration of the program. Automatic variables get initialized every time the program enters their scope and gets stored at a new memory location each time.

7 - Difference between fork-join, fork-join_any, and fork-join_none

All fork allow processes inside of it to execute in parallel.

However, fork-join waits for all processes to finish before moving on to consequent code.

Fork-join_any waits for any one of the processes to finish before moving on to consequent code.

Fork-join_none starts all of the processes but immediately moves onto the consequent code.

6 - What is semaphore and in what scenario is it used?

Semaphores allows one process to get control of execution of the code (grab a lock). It is used when multiple threads/processes could execute the same task and parallel and they should not be able to do that.
I also would see it when I step through code in vivado when I am putting and getting objects from a mailbox.

5 - What is DPI? Explain DPI export and import.

DPI allows us to write functions in C or C++, compile them into a dll, import the dll using DPI and then use that dll in our testbench. This is useful when we want to write a model in C++ or C to calculate expected results of outputs.

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

:: specifies the scope where an item should be searched in.

1 - How will you test the functionality of interrupts using functional coverage?

I define the types of interrupts I want to test. Then randomize those types and apply the stimulus to the dut. Then I would collect the results and compare with expected.
