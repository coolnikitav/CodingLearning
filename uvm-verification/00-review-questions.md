# Review

## Set 2
2. What does a sequence normally contain?
   - It typically contains inputs that will be applied to the DUT as well as some metadata that will help us determien what to apply.
1. Write pseudo code for implementing an AHB-Lite driver.
   ```
   class ahb_driver extends uvm_driver;
      `uvm_component_utils(ahb_driver)

      function void build_phase(string path);
         super.new(ahb_driver, path);
      endfunction
   
      virtual task run_phase()
         forever() begin
            # send signal to slave
         end
      endtask
   endclass
   ```

## Set 1
1. What is a UVM RAL mode? Why is it required?
   - RAL is register abstraction layer. It is used to write to the registers of the DUT. Without it, a transaction would need to be created and passed to the DUT, resulting in a cumbersome process.
  
2. What is p_sequencer, and wehere is it used?
   - p_sequencer is a handle to the sequencer on which the current sequence should be executed.
  
3. What is an analysis port?
   - An analysis port is used to send information from monitor to scoreboard to analyze it and compare it to golden data.
  
4. What is the difference between new() and create()?
   - The only thing I know is that new() is used in constructor and i acted upon the top class by using super.new(). Create is used when creating objects in build_phase usually.
  
5. Is UVM independent of SystemVerilog?
   - Not sure what this question is asking. UVM uses SystemVerilog language.
  
6. Why do we need to register a class with a factory?
   - So we can use UVM methods with it.
  
7. What are Active and Passive modes in an agent?
   - Active mode uses both monitor and scoreboard. Passive only uses monitor.

8. What is a TLM Fifo?
   - TLM: Transaction level modeling. Fifo stores sender's sends and then gives the to the receiver when requested.
  
9. What are the advantages of 'uvm_component_utils and 'uvm_object_utils?
   - Objects are dynamic, used for changing components, like transactions. Components are static, like driver, monitor, scoreboard. Component is derived from object. Thus, object has all functionality of a component and more.
  
10. How does a sequence start?
    - A transaction is created. Then the sequence is started with start_item(tr). It is ended with finish_item(tr);
