# TLM (Transaction Level Modeling)

## Fundamentals
- Q1: What is a sequencer?
- Q2: What does TLM use instead of classes?
  
Sequencer is uvm's generator.

- Sequencer -> Driver : Special TLM Port : SEQ_ITEM_PORT
- Monitor -> Scoreboard : TLM Port : UVM_ANALYSIS PORT

TLM does not use classes. We use port(initiator) and export(responder)

- Put operation: Initiator A sends data to responder B.
- Get operation: Initiator A gets data from responder B.
- Transport operation: Data flows back and forth between A and B.

All of these operations can be implemented in a blocking or nonblocking manner.

## Blocking PUT Operation P1
- Q: What are the 3 functions? Write them out.
  
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f3ba0f99-25c0-4da4-ae73-1039831d21ab)

- uvm_blocking_put_port #(parameter) // parameter is the type of data you are communicating
- uvm_blocking_put_export #(parameter)
- uvm_blocking_put_imp #(parameter)  // implementation
