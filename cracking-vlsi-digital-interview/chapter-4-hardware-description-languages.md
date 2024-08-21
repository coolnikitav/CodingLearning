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
