## Set 2
10. Difference between structure and class.
   - By default, a structure is public and a class is private.
9. Difference between dynamic array and queue.
   - Dynamic array is an array which size is specified in runtime. Besides that it functions like a regular array. A queue behaves like a queue. You can push items to the back and pull them from the front.
8. Explain the cycle of verification and its closure.
   - Create a test plan, write the testbench, look at results.
7. What is layered architecture in verification?
   - classes containing other classes. Example: environment contains generator, driver, monitor, scoreboard.
6. How to ensure address range 0x2000 to 0x9000 is covered in simulations?
   - Set a constraint that includes values in this range.
5. What are 2 state and 4 state variables? Provide some examples.
   - 2 state variables can take on values of 1 and 0. Example: bit. 4 state variables can take on a value of 1,0,x,z. Example: reg,logic.
4. What is ignore_bins?
   - Ignore values in the existing bins. Very useful when existing bins cover a range.
3. Difference between code and functional coverage?
   - Functional coverage is checking to make sure that all features of the design are covered. Code coverage is the process of checking that all of the code in the DUT has been ran through.
2. How to disable constraints?
   - constraint.disable();
1. What is the difference between a depp copy and a shallow copy?
   - A deep copy points to the original object. A shallow copy creates a new object. When a change is made to the deep copy, it is reflected on the original. On the other hand, when a change is made to the shallow copy, the change is not reflected on the original.

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
