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
```
module tb;
  
  bit [31:0] arr[10];
  
  initial begin
    fill_arr(arr);
    print(arr);
    
  end
  
  task fill_arr(output bit [31:0] arr[10]);
    for (int i = 0; i < 10; i++) begin
      arr[i] = $pow(i,2);  
    end  
  endtask
  
  task print(input bit [31:0] arr[10]);
    for (int i = 0; i < 10; i++) begin
      $display("arr[%0d] : %0d", i, arr[i]);  
    end     
  endtask
  
endmodule
```
## Loops
- for loop
- repeat
- foreach

Loops need to be in procedural statements, like initial or always
```
module tb;
  
  int arr[10];
  int i;
  
  initial begin
    for (i = 0; i < 10; i++) begin
      arr[i] = i;
    end
    
    $display("arr : %0p", arr);
    
  end
  
endmodule
```
```
module tb;
  
  int arr[10];
  
  initial begin
    foreach(arr[i]) begin  // 0-9
      arr[i] = i;
      $display("%0d",arr[i]);
    end	
  end 
  
endmodule
```
```
module tb;
  
  int arr[10];
  int i = 0;
  
  initial begin
    repeat(10) begin
      arr[i] = i;
      i++;
    end
    
    $display("arr : %0p",arr);
    
  end 
  
endmodule
```
## Array operations

### Copy
Array must be the same size and store the same datatypes
```
module tb;
  
  int arr1[5];
  int arr2[5];
  
  initial begin
    for (int i=0; i<5; i++) begin
      arr1[i] = 5*i;  // 0 5 10 15 20
    end
    
    arr2 = arr1;  // copy
    
    $display("arr1 : %0p", arr1);
    $display("arr2 : %0p", arr2);
    
  end
  
endmodule
```

## Compare
Compares element by element to see whether they are equal.

Arrays must be the same size and store the same data type.

Arrays are equal:

```
module tb;
  
  int arr1[5] = {1,2,3,4,5};
  int arr2[5] = {1,2,3,4,5};
  
  int status;
  
  initial begin
    status = arr1 == arr2;
    
    $display("status : %0d", status);
    
    if (status)
      $display("arrays are equal");
    else
      $display("arrays are not equal");        
  end
  
endmodule
```

Arrays are not equal:

```
module tb;
  
  int arr1[5] = {1,2,3,4,5};
  int arr2[5] = {1,2,2,4,5};
  
  int status;
  
  initial begin
    status = (arr1 != arr2);
    
    $display("status : %0d", status);
    
    if (status)
      $display("arrays are not equal");
    else
      $display("arrays are equal");        
  end
  
endmodule
```

## Dynamic Arrays
```
module tb;
  
  int arr[];
  
  initial begin
    arr = new[5];
    
    for (int i = 0; i < 5; i++) begin
      arr[i] = 5*i;
    end
    
    $display("arr : %0p", arr);  // 0 5 10 15 20
    
    arr.delete();
    
  end
  
endmodule
```
```
module tb;
  
  int arr[];
  
  initial begin
    arr = new[5];
    
    for (int i = 0; i < 5; i++) begin
      arr[i] = 5*i;
    end
    
    $display("arr : %0p", arr);  // 0 5 10 15 20
    
    arr = new[30];
    $display("arr : %0p", arr);  // 0..0 0 0 0 0
    
  end
  
endmodule
```
```
module tb;
  
  int arr[];
  
  initial begin
    arr = new[5];
    
    for (int i = 0; i < 5; i++) begin
      arr[i] = 5*i;
    end
    
    $display("arr : %0p", arr);  // 0 5 10 15 20
    
    arr = new[30](arr);
    $display("arr : %0p", arr);  // 0 5 10 15 20 0 0 ... 0
    
  end
  
endmodule
```
```
module tb;
  
  int arr[];
  int fixed_size_arr[30];
  
  initial begin
    arr = new[5];
    
    for (int i = 0; i < 5; i++) begin
      arr[i] = 5*i;
    end
    
    $display("arr : %0p", arr);  // 0 5 10 15 20
    
    arr = new[30](arr);
    $display("arr : %0p", arr);  // 0 5 10 15 20 0 0 ... 0
    
    fixed_size_arr = arr;  // fixed size array must be the same size
    $display("fixed_size_arr : %0p", fixed_size_arr);  // 0 5 10 15 20 0 0 ... 0
    
  end
  
endmodule
```

## Queue
```
module tb;
  
  int queue[$];
  int j = 0;
  
  initial begin
    queue = {1,2,3};
    $display("queue: %0p", queue);
    
    queue.push_front(7);
    $display("queue: %0p", queue);
    
    queue.push_back(9);
    $display("queue: %0p", queue);
    
    queue.insert(2,10);
    $display("queue: %0p", queue);
    
    j = queue.pop_front(); // j needs to be same type as elements
    $display("queue: %0p", queue);
    $display("j: %0d", j);
    
    j = queue.pop_back();
    $display("queue: %0p", queue);
    $display("j: %0d", j);
    
    queue.delete(1);
    $display("queue: %0p", queue);
    
  end
  
endmodule
```

