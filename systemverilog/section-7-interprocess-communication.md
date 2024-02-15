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
