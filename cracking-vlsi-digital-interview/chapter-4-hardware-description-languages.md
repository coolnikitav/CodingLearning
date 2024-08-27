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
