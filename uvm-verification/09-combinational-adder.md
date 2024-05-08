# Combinational Adder

## Summary of the Verification Environment
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f92bbe5c-e194-4498-80aa-a812a046d78c)

- Driver will request for a sequence and the sequencer will send it.
- Monitor will forward DUT output to the scoreboard with the help of UVM_ANALYSIS_PORT

Classes:
- Transaction: keep track of all the I/O present in DUT (uvm_sequence_item)
- Sequence: combination of transactions to verify specific test case (uvm_sequence)
- Sequencer: manage sequences. Send sequence to driver after request(uvm_sequencer)
- Driver: send request to driver for sequence, apply sequence to the DUT (uvm_driver)
- Monitor: collect response fo DUT and forward to scoreboard (uvm_monitor)
- Scoreboard: compare response with golden data (uvm_scoreboard)
- Agent: Encapsulate Driver, Sequence, Monitor. Connection of driver and sequencer TLM port (uvm_agent)
- Env: Encapsulate Agent and Scoreboard. Connection of analysis port of MON, SCO (uvm_env)
- Test: Encapsulate Env. start sequence (uvm_test)

## Verification of Combinational Adder: DUT
```
`timescale 1ns / 1ps

module add(
    input  [3:0] a, b,
    output [4:0] y
    );
    assign y = a + b;    
endmodule

interface add_if();
    logic [3:0] a,b;
    logic [4:0] y;
endinterface
```
