## Questions
- Q: In systemverilog, class can be defined inside:
  - Program
  - Module
  - Package
  - All the above
- A: All the above

- Q: Can a logic variable have multiple drivers?
- A: No

- Q: Which of the following are true,
  - Interface can contain module instance
  - Module can contain class
  - Program can contain package
  - Program can contain class
- A: Module can contain class, program can contain package, program can contain class

- Q: Can a wire variable have multiple drivers?
- A: Yes

- Q: What will be the output of code below?
```
module tb;
  class abc;
    int sum;
    function int calc(input int a, input int b);
      this.sum = a + b;
      return sum;
    endfunction
  endclass
  
  initial begin
    abc obj1, obj2;
    obj1 = new();
    obj2 = new();
        
    obj1.sum = obj1.calc(10, 20);
    obj2.sum = obj2.calc(30, 40);
    
    $display("obj1 sum = %0d, obj2 sum = %0d", obj1.sum, obj2.sum);
  end
endmodule
```
  - obj1 sum = 70, obj2 sum = 70
  - obj1 sum = 30, obj2 sum = 70
  - obj1 sum = 0, obj2 sum = 0
  - obj1 sum = 70, obj2 sum = 30
- A: obj1 sum = 70, obj2 sum = 70

- Q: array[4][8] this array declaration is,
  - Compact declaration
  - Verbose declaration
  - Single dimension array declaration
  - None of the above
- A: Verbose declaration

- Q: Which of the following is suitable for asynchronous signals
  - Modport
  - Either modport or clocking block
  - Clocking block
  - Both modport and clocking block

## Set 4
10. What is the purpose of this pointer in SystemVerilog?
   - To indicate that its pointing to the variable in this class when name of a parameter is the same.
9. What is polymorphism and its advantage?
   - Objects can be changed with functions from other classes. Its advantage is that everything can be more modularized and instead of chaning the original function, you can extend it with new functionality.
8. What are teh default values of variables in the SystemVerilog?
   - logic/reg/wire: x, bit/int: 0
7. Difference between initial and final block.
   - I know that initial executes in the beginning of the simulation.
   - I am assuming final executes in the end after everything has been executed.
6. What are pass-by-value and pass-by-reference method.
   - Pass-by-value operates with a shallow copy, which is a simple copy of the value of variable. Changes to the shallow copy do not change the original variable
   - Pass-by-reference operates with a deep copy. Changes to the deep copy will change the original variable
5. Give an example of a function call inside a constraint.
   ```
    constraint a_cntrl {
        a inside [calc_lower_bound(a):calc_upper_bound(a)];
    }
   ``
4. How to find indices associated with associative array items?
   - I am assuming something like array.keys()
3. What are the types of assertions?
   - I only know assert
2. What will be your approach if functional coverage is 100% but code coverage is too low?
   - I will try to remove the code that is not being used.
1. Is it possible to override existing constraints?
   - You can turn off existing constraints and turn other ones on. I am not sure about override.

## Set 3
10. How can you establish communication between monitor and scoreboard in SystemVerilog?
    - By creating a mailbox that you put stuff in in the monitor and get stuff from in the scoreboard.
9. What are parameterized classes?
    - Classes with parameters that can be used for variables and functions inside.
8. Write a constraint to have a variable divisible by 5.
   ```
   constraint a_div_5 {
      a % 5 == 0;
   }
   ```
7. Differences between integer and int.
   - Both are 32 bit signed int. But int can take on values of 0,1, while integer can take on values of (0,1,x,z)
6. Explain bidirectional constraints.
   - Bidirectional constraints are used to specify one variable's dependance on another.
5. Difference between while and do while.
   - While checks condition and then does something. do while does something and then checks the condition.
4. Why do we need randomization in SystemVerilog?
   - So we can apply random stimulus and improve our testing procedures.
3. Difference between virtual and pure virtual function
   - Virtual function is a function that is defined in the base class and can be overwritten in the derived class.
   - Pure virtual function is a function that is instantiated, but not defined in the base class. It must be defined in the derived class.
2. Difference between static and dynamic casting
   - dynamic used $cast and is a run-time operation. It is more complex and less efficient than static, but it is safer and handles errors.
   - static uses newDataType'(variable) and is compile-time operation
1. What is a virtual function?
   - Virtual function is a function that can be overwritten in a derived class.

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
