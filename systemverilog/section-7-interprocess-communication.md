# Interprocess communication

## Interprocess communication 
- Event
  - Convey message between classes
  - -> / @ / wait
- Semaphore
  - Access resources of tb_top
  - get / put
- Mailbox
  - Send transaction data between classes
  - get / put
 
### Events
```
// Trigger: ->
// edge sensitive_blocking @(), level_sensitive_non-blocking wait()

module tb;
  
  event a;
  
  initial begin
    #10;
    -> a;  // trigger an event
  end
  
  initial begin
    @(a);
    $display("Received event at %0t", $time); // Received event at 10
  end
  
endmodule
```
```
// Trigger: ->
// edge sensitive_blocking @(), level_sensitive_non-blocking wait()

module tb;
  
  event a;
  
  initial begin
    #10;
    -> a;  // trigger an event
  end
  
  initial begin
    wait(a.triggered);
    $display("Received event at %0t", $time); // Received event at 10
  end
  
endmodule
```
@ vs wait
```
module tb;
  
  event a1,a2;
  
  initial begin
    -> a1;
    #10;
    -> a2;
  end
  
  initial begin
    wait(a1.triggered);
    $display("Event a1 trigger");  // Event a1 trigger
    @(a2);
    $display("Event a2 trigger");  // Event a2 trigger
  end
  
endmodule
```
## Executing multiple processes
### Multiple processes with multiple initial blocks
```
module tb;
  
  int data1, data2;
  event done;
  
  // Generator
  initial begin
    for (int i = 0; i < 10; i++) begin
      data1 = $urandom();
      $display("Data sent : %0d", data1);
      #10;
    end
    -> done;
  end
  
  // Driver
  initial begin
    forever begin  // repeat until the end of the simulation
      #10;
      data2 = data1;
      $display("Data received : %0d", data2);
    end
  end
  
  //////
  initial begin
    wait(done.triggered);
    $finish;
  end

endmodule
```
### Multiple processes with fork join
```
module tb;
  
  int i = 0;
  bit [7:0] data1,data2;
  event done;
  event next;
  
  task generator();
    for (i = 0; i < 10; i++) begin
      data1 = $urandom();
      $display("Data sent at time %0t : %0d", $time, data1);
      #10;
      wait(next.triggered);
    end
    -> done;
  endtask
  
  task receiver();
    forever begin
      #10;
      data2 = data1;
      $display("Data received at time %0t: %0d", $time, data2);
      -> next;
    end
  endtask
  
  task wait_event();
    wait(done.triggered);
    $display("Completed sending all stimulus");
    $finish();
  endtask
  
  initial begin
    // all statements inside of fork join execute in parallel
    fork
      // these statements can be in any order
      generator();
      receiver();
      wait_event();
    join
    
    // following statements will not be executed until fork join is finished
  end
  
endmodule
```
```
# KERNEL: Data sent at time 0 : 167
# KERNEL: Data received at time 10: 167
# KERNEL: Data sent at time 10 : 220
# KERNEL: Data received at time 20: 220
# KERNEL: Data sent at time 20 : 248
# KERNEL: Data received at time 30: 248
# KERNEL: Data sent at time 30 : 81
# KERNEL: Data received at time 40: 81
# KERNEL: Data sent at time 40 : 94
# KERNEL: Data received at time 50: 94
# KERNEL: Data sent at time 50 : 101
# KERNEL: Data received at time 60: 101
# KERNEL: Data sent at time 60 : 180
# KERNEL: Data received at time 70: 180
# KERNEL: Data sent at time 70 : 205
# KERNEL: Data received at time 80: 205
# KERNEL: Data sent at time 80 : 227
# KERNEL: Data received at time 90: 227
# KERNEL: Data sent at time 90 : 151
# KERNEL: Data received at time 100: 151
```
```
module tb;
  
  task first();
    $display("Task 1 started at %0t", $time);
    #20;
    $display("Task 1 completed at %0t", $time);
  endtask
  
  task second();
    $display("Task 2 started at %0t", $time);
    #30;
    $display("Task 2 completed at %0t", $time);
  endtask
  
  task third();
    $display("Reached next to join at %0t", $time);
  endtask
  
  initial begin
    fork
      first();
      second();
    join
      third();
  end
  
endmodule
```
```
# KERNEL: Task 1 started at 0
# KERNEL: Task 2 started at 0
# KERNEL: Task 1 completed at 20
# KERNEL: Task 2 completed at 30
# KERNEL: Reached next to join at 30
```
### Fork join_any
As soon as one of the processes in fork join execute, the following statement will get executed.
```
module tb;
  
  task first();
    $display("Task 1 started at %0t", $time);
    #20;
    $display("Task 1 completed at %0t", $time);
  endtask
  
  task second();
    $display("Task 2 started at %0t", $time);
    #30;
    $display("Task 2 completed at %0t", $time);
  endtask
  
  task third();
    $display("Reached next to join at %0t", $time);
  endtask
  
  initial begin
    fork
      first();
      second();
    join_any
      third();
  end
  
endmodule
```
```
# KERNEL: Task 1 started at 0
# KERNEL: Task 2 started at 0
# KERNEL: Task 1 completed at 20
# KERNEL: Reached next to join at 20
# KERNEL: Task 2 completed at 30
```
### Fork join_none
Doesn't wait for any process to complete inside of fork join (non-blocking).
```
module tb;
  
  task first();
    $display("Task 1 started at %0t", $time);
    #20;
    $display("Task 1 completed at %0t", $time);
  endtask
  
  task second();
    $display("Task 2 started at %0t", $time);
    #30;
    $display("Task 2 completed at %0t", $time);
  endtask
  
  task third();
    $display("Reached next to join at %0t", $time);
  endtask
  
  initial begin
    fork
      first();
      second();
    join_none
      third();
  end
  
endmodule
```
```
# KERNEL: Reached next to join at 0
# KERNEL: Task 1 started at 0
# KERNEL: Task 2 started at 0
# KERNEL: Task 1 completed at 20
# KERNEL: Task 2 completed at 30
```
## Semaphore
```
class first;
  
  rand int data;
  
  constraint data_c {data < 10; data > 0;}
  
endclass

class second;
  
  rand int data;
  
  constraint data_c {data > 10; data < 20;}
  
endclass

class main;
  
  semaphore sem;
  
  first f;
  second s;
  
  int data;
  int i = 0;
  
  task send_first();
    sem.get(1);  // ensures that only 1 task can execute its critical section at a time
    for (i = 0; i < 10; i++) begin
      f.randomize();
      data = f.data;
      $display("First access semaphore and data sent : %0d", f.data);
      #10;
    end
    sem.put(1);
    $display("Semaphore unoccupied");
  endtask
  
  task send_second();
    sem.get(1);
    for (i = 0; i < 10; i++) begin
      s.randomize();
      data = s.data;
      $display("Second access semaphore and data sent : %0d", s.data);
      #10;
    end
    sem.put(1);
    $display("Semaphore unoccupied");
  endtask
  
  task run();
    sem = new(1);
    f = new();
    s = new();
    
    fork
      send_first();
      send_second();
    join
  endtask
  
endclass

module tb;
  
  main m;
  
  initial begin
    m = new();
    m.run();
  end
  
  initial begin
    #250;
    $finish();
  end
  
endmodule
```
```
# KERNEL: First access semaphore and data sent : 4
# KERNEL: First access semaphore and data sent : 6
# KERNEL: First access semaphore and data sent : 1
# KERNEL: First access semaphore and data sent : 9
# KERNEL: First access semaphore and data sent : 2
# KERNEL: First access semaphore and data sent : 2
# KERNEL: First access semaphore and data sent : 3
# KERNEL: First access semaphore and data sent : 6
# KERNEL: First access semaphore and data sent : 1
# KERNEL: First access semaphore and data sent : 3
# KERNEL: Semaphore unoccupied
# KERNEL: Second access semaphore and data sent : 13
# KERNEL: Second access semaphore and data sent : 15
# KERNEL: Second access semaphore and data sent : 11
# KERNEL: Second access semaphore and data sent : 12
# KERNEL: Second access semaphore and data sent : 16
# KERNEL: Second access semaphore and data sent : 14
# KERNEL: Second access semaphore and data sent : 17
# KERNEL: Second access semaphore and data sent : 11
# KERNEL: Second access semaphore and data sent : 17
# KERNEL: Second access semaphore and data sent : 12
# KERNEL: Semaphore unoccupied
```
## Mailbox
```
class generator;
  
  int data = 12;
  mailbox mbx;  // gen2drv
  
  task run();
    mbx.put(data);
    $display("[GEN] : SENT DATA : %0d", data);
  endtask
  
endclass

class driver;
  
  int datac = 0;  
  mailbox mbx;
  
  task run();
    mbx.get(datac);
    $display("[DRV] : RCVD DATA : %0d", datac);
  endtask
  
endclass

module tb;
  
  generator gen;
  driver drv;
  mailbox mbx;
  
  initial begin
    gen = new();
    drv = new();
    mbx = new();
    
    gen.mbx = mbx;
    drv.mbx = mbx;
    
    gen.run();
    drv.run();
  end
  
endmodule
```
```
# KERNEL: [GEN] : SENT DATA : 12
# KERNEL: [DRV] : RCVD DATA : 12
```
### Specifying mailbox with a custome constructor
```
class generator;
  
  int data = 12;
  mailbox mbx;  // gen2drv
  
  function new(mailbox mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
    mbx.put(data);
    $display("[GEN] : SENT DATA : %0d", data);
  endtask
  
endclass

class driver;
  
  int datac = 0;  
  mailbox mbx;
  
  function new(mailbox mbx);
    this.mbx = mbx;
  endfunction
  
  task run();
    mbx.get(datac);
    $display("[DRV] : RCVD DATA : %0d", datac);
  endtask
  
endclass

module tb;
  
  generator gen;
  driver drv;
  mailbox mbx;
  
  initial begin
    mbx = new();
    
    gen = new(mbx);
    drv = new(mbx);  
    
    gen.run();
    drv.run();
  end
  
endmodule
```
