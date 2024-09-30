# Hardware Description Languages

## Verilog

## SystemVerilog

### 208. What is the difference between a reg, wire and logic in SystemVerilog?
- a wire is used for continuous assignment. They represent physical wires used to connect 2 elements. Can only be used to model combinational logic.
- a reg is used to store data. They cannot be driven by continuous assignment. Can be used for sequential or combinational logic.
- logic is used to provide flexibility to the user, so the variable can be either reg or wire

### 209. What is the difference between a bit and logic data type?
- bit is a 2-state variable (0,1). Logic is a 4-state variable (0,1,X,Z)

### 210. What is the difference between logic[7:0] and byte variable in SystemVerilog?
- logic would be unsigned, byte would be signed.

### 211. Which of the array types: dynamic array or associative array, are good to model really large array, say: a huge memory array of 32KB.
- Associative array would be better because it doesn't actually allocate all of that memory. It behaves more like a hash map and will mainly only allocate the memory you are using.

### 212. Supposed a dynamic array of integers (myvalues) is initialized to values as shown below. Write a code to find all elements greater than 3 in the array using array locator method "find"? 
```
module top;
  int myvalues[] = '{9,1,8,3,2,4,6};
    
  initial begin
    int greater_than_3[$] = myvalues.find(x) with (x>3);
    $display("greater_than_3: %0p", greater_than_3);
  end
endmodule
```

### 213. What is the difference between a struct and a union in SystemVerilog?
- A struct is a structure that can have elements of different data types. The memory needed for a struct is equal to the sum of the elements.
- A union is a structure that can have elements of different data types, except they share the same memory location. The memory needed for a union is the largest memory that any of the elements require. Unions can be useful when we want to model a hardware resource that can store values, like a register.

```
module union_example;
  typedef union {
    bit[15:0] salary;
    integer id;
  } employee;
    
  initial begin
    employee emp;
    emp.salary = 'h800;
    $display("salary updated for EMP: %p", emp);
    emp.id     = 'd1234;
    $display("ID updated for EMP: %p", emp); //Note: Salary information will be lost
  end
endmodule
```

### 214. What is the concept of "ref" and "const ref" argument in SystemVerilog function or task?
- ref is used when we want to pass by reference (pass the variables address) instead of making a copy of it. Making a copy of a large array is resource intensive.
- const is added if we don't want the user to be able to modify the variable in the function or task.

### 215. What would be the direction of arguments a and b in the following:
```
task sticky(ref int array[50], int a, b);
```
- a and b are ref
- there are 4 types of arguments: input, output, inout, ref. The default is input

### 216. What is the difference between a packed array and an unpacked array?
- packed: bit [7:0] mem;  Packed array represents a contiguous set of bits. Packed arrays can be made of only the single bit data types (bit, logic, reg), or enumerated types.
- unpacked: bit mem [7:0]; Doesn't need to be represented as a contiguous set of bits. Unpacked array can be made of any data type. If you want to perform operations on multiple bits, you have to do them one by one. You cant use a range like arr[7:4] = 4'b1010 or arr = ~arr

### 217. What is the difference between a packed and unpacked struct?
- packed: all elements can be represented in bits, so they can all be packed next to each other as a contiguous block of memory
- unpacked: elements are stored in different places in memory

### 218. Which of these statements is true?
- Functions should execute in zero simulation time.
- Tasks should execute in zero simulation time.
- True
- False

### 219. Given a dynamic array of size 100, how can the array be re-sized to hold 200 elementes while the lower 100 elements are preserved as original?
```
int arr[];
arr = new[100];
arr = new[200](arr);
```

### 220. What is the difference between forever and for in SystemVerilog?
- forever will repeat its loop until the simulation ends. A break statement can be used to break out of a for loop.
- for will repeat its loop specified number of times.

### 221. What is the difference between "case", "casex" and "casez" in SystemVerilog?
- A case statement needs an exact match.
- casex supports ?, z, x as don't care characters
- casez supports ?, z as don't care characters

### 222. Which of the logical equality operators "==" or "===" are used in case expression conditions for case, casex, and casez?
- === is used

### 223. What is the difference between $display, $write, $monitor and $strobe in SystemVerilog?
- $display prints to the console and adds a newline char to the end
- $write prints to the console without a newline char
- $monitor print to the console every time one of its variable changes
- $strobe prints the last updated value at the end of the time step. Typically the next $display would print this value

### 224. What is wrong with following SystemVerilog code?
```
task wait_packet;
  Packet packet;
  event packet_received;
  @packet_received;
  packet = new();
endtask

function void do_print();
  wait_packet();
  $display("packet received")
endfunction
```

You cannot have any construct that consumes time in a function.

### 225. What is the difference between new() and new[] in SystemVerilog?
- new() is a constructor for an object
- new[] is used to allocate memory for dynamic arrays

### 226. What is the concept of forward declaration of a class in SystemVerilog?
- Forward declaration is used to prevent a compiler error when class might reference another class before it is defined:
```
typedef class DEF;

class ABC;
  DEF def;  // typedef prevents from a compiler error being thrown here
endclass

class DEF;
  ABC abc;
endclass
```

### 227. Analyze the following code and explain if there are any issues with code?
```
task gen_packet(Packet pkt);
  pkt = new();
  pkt.dest = 0xABCD;
endtask

Packet pck;
initial begin
  gen_packet(pkt);
  $display(pkt.dest);
end
```
- There will be a null-pointer runtime error. The object is passed by value into the task. It creates an object local to the task and modifies its property. When $display is called outside of the task, it is called on a property that wasn't set.

### 228. What is the difference between private, public, and protected data members of a SystemVerilog class?
- private - only accessible in the current class. The word "local" is used to indicate that its private
- public - accessible by other classes
- protected - only accessible in class and by derived classes

### 229. Are SystemVerilog class members public or private by default?
- They are public by default.

### 230. What is a nested class and when would you use a nested class?
- A class defined inside of a class. Used when the object you want to create should only be specific to the object its in.
```
class StringList;
  class Node;
    string name;
    Node link;
  endclass
endclass
```

### 231. What are interfaces in SystemVerilog?
- Interfaces are used to give users access to outputs and inputs of modules without directly having access to the internal code. It helps in communication between design blocks by connecting using a single name instead of having all the port names and connections.

### 232. What is a modport construct in an interface?
- Modport is a construct that lets you group signals and specify their directions. They are needed because by default nets are inout. So if two modules are driving it with different values, you can have a value of X.

### 233. Are interfaces synthesizable?
- Yes, interfaces are synthesizable.

### 234. What is a clocking block and what are the benefits of using clocking blocks inside an interface?
- A clocking block let's you define clock behavior for you signals, so the rest of the code can be focused on transactions and logical behavior. It can only be declared inside of a module or an interface.
```
clocking c1 @ (posedge clk);
  default input #1step output #4;
  input a;
  output b;
endclocking
```

### 235. What is the difference between the following two ways of specifying skews in a clocking block?
```
1) input #1step req1;
2) input #1ns req1;
```
- The first one, the input will be sampled one timestep before the clock edge. In the second one, it will be sampled 1ns before the clock edge.

### 236. What are the main regions inside a SystemVerilog simulation time step?
- Preponed, active, observed, reactive, postponed
- Preponed is to evaluate the inputs. It is executed only once
- Active consists of active, inactive, and NBA (non-blocking assignments). RTL and behavioral code are scheduled, as well as non-blocking statements are evaluated, in the active region. Blocking statements and assignments with #0 delays are executed in the inactive region. Evaluation of RHS happens in the active region.
- Observed region is for evaluation of property expressions (used in concurrent assertions).
- Reactive region is used to schedule blocking assignments, #0 delay assignments, and nonblocking assignments.
- Postponed region is for events like $monitor and $strobe to be executed in this region. $display events are scheduled for execution in Active and Reactive regions.

### 237. Given following constraints, which of the following options are wrong?
```
rand logic [15:0] a, b, c;
constraint c_abc {
  a < c;
  b == a;
  c < 30;
  b > 25;
}

1) b can be any value between 26 and 29
2) c can be any value between 0 and 29
3) c can be any value between 26 and 29
```
- 2 and 3 are wrong. c cannot be 25 or less because b needs to be less than c and greater than 25
