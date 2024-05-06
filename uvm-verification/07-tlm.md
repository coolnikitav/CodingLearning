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
