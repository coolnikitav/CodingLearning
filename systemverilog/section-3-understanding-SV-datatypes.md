# Understanding SystemVerilog Datatypes

## Datatypes
- Handle hardware
  - reg (popular in procedural)
  - wire (popular in continous)
- Add a variable
  - fixed point
    - 2 state: 0,1
      - signed: 8-bit byte, 16-bit shortint, 32-bit int, 64-bit longint
      - unsigned: bit[7:0], bit[15:0], bit[31:0] = int unsigned
    - 4 state: 0,1,x,z: integer = 32-bit signed
  - floating point (real: 64 bit double precision)
- For simulation
  - Fixed point time: time -> 64-bit
  - Float point time: reatltime -> 64 bit

reg cannot be output of a module

## Arrays
```
module tb;
  
  // single bit size, 8 elements (fixed size)
  bit arr1[8];  // bit arr1[7:0];
  bit arr2[] = {1,0,1,1};
  
  initial begin
    $display("Size of arr1 : %0d", $size(arr1));
    $display("Size of arr2 : %0d", $size(arr2));
    
    $display("Value of first element : %0d", arr1[0]);
    arr1[1] = 1;
    $display("Value of second element : %0d", arr1[1]);
    
    $display("Value of all elements of arr2 : %0p", arr2);
  end
  
endmodule
```

Array initialization
- Unique values: arr[] = {1,2,3,4};
- Repetitive values: arr[] = {6{1}};
- Default value: arr[] = {default: 0};
- Uninitialized: arr[8];

```
bit arr[5];  // 2-state data type
  
  initial begin
    $display("arr : %0p", arr);  // 0 0 0 0 0
  end
```
```
logic arr[5];  // 4-state data type
  
  initial begin
    $display("arr : %0p", arr);  // x x x x x
  end
```
```
int arr[5] = {1,2,3,4,5};
  
  initial begin
    $display("arr : %0p", arr);  // 1 2 3 4 5
  end
```
```
int arr[5] = {1,2,3,4};  // error
  
  initial begin
    $display("arr : %0p", arr);
  end
```
```
int arr[5] = `{5{0}};
  
  initial begin
    $display("arr : %0p", arr);  // 0 0 0 0 0
  end
```
```
int arr[10] = `{default : 2};
  
  initial begin
    $display("arr : %0p", arr);  // 2 2 2 2 2 2 2 2 2 2
  end
```
```
// unique
  int arr1[2] `{1,2};
	
  // repetition operator
  int arr2[2] = `{2{3}};
  
  //default
  int arr3[2] = `{default : 2};
  
  // uninitialized
  int arr4[2];
```
