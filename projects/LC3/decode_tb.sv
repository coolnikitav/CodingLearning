`timescale 1ns / 1ps

/////////////////////////////////

import "DPI-C" function void DecodeIR(
    input  logic [15:0] instruction,
    output byte         W_Control,
    output byte         E_Control,
    output byte         E_Control_Valid
);

/////////////////////////////////

interface decode_if;
    logic        clk;
    logic        rst;
    logic [15:0] npc_in;
    logic        enable_decode;
    logic [15:0] Imem_dout;
    logic [15:0] IR;
    logic [15:0] npc_out;
    logic [1:0]  W_Control;
    logic [5:0]  E_Control;
endinterface

/////////////////////////////////

package op_pkg;
    typedef enum { reset, decode, no_update} op_t;
endpackage

import op_pkg::*;

/////////////////////////////////

class transaction;
    rand op_t        op;
    rand bit  [15:0] npc_in;
         bit         enable_decode;
    rand bit  [15:0] Imem_dout;
     
         bit  [15:0] IR;
         bit  [15:0] npc_out;
         bit  [1:0]  W_Control;
         bit  [5:0]  E_Control;
    
    function transaction copy();
        copy = new();
        copy.npc_in        = this.npc_in;
        copy.enable_decode = this.enable_decode;
        copy.Imem_dout     = this.Imem_dout;
        copy.IR            = this.IR;
        copy.npc_out       = this.npc_out;
        copy.W_Control     = this.W_Control;
        copy.E_Control     = this.E_Control;
    endfunction
    
    constraint op_cntrl {
        op dist { 
                  op_pkg::reset     := 10, 
                  op_pkg::decode    := 90,
                  op_pkg::no_update := 10 
                };
    }
endclass

/////////////////////////////////

class generator;
    transaction trans;
    mailbox #(transaction) gdmbx;  // gen -> drv
    
    event drvnext;
    event sconext;
    event done;
    
    int count = 0;
    
    function new(mailbox #(transaction) gdmbx);
        this.gdmbx = gdmbx;
    endfunction
    
    task run();
        repeat (count) begin
            trans = new();
            assert(trans.randomize()) else $error("RANDOMIZATION FAILED");
            $display("[GEN]: op: %s | npc_in: %0h | Imem_rdout: %0hb", trans.npc_in, trans.enable_decode, trans.Imem_dout);
            
            gdmbx.put(trans.copy());
            
            @(drvnext);
            @(sconext);
        end
        -> done;
    endtask
endclass

/////////////////////////////////

class driver;
    transaction gdtrans;
    transaction dstrans;
    mailbox #(transaction) gdmbx;  // gen -> drv
    mailbox #(transaction) dsmbx;  // drv -> sco
    virtual decode_if vif;
    
    event drvnext;
    
    function new(mailbox #(transaction) gdmbx, mailbox #(transaction) dsmbx);
        this.gdmbx = gdmbx;
        this.dsmbx = dsmbx;
    endfunction
    
    task reset();
        @(posedge vif.clk);
        vif.rst           <= 1'b1;
        vif.npc_in        <= 16'b0;
        vif.enable_decode <= 1'b0;
        vif.Imem_dout       <= 16'b0;
        
        @(posedge vif.clk);
        vif.rst           <= 1'b0;
        
        dstrans.IR        <= 16'b0;
        dstrans.npc_out   <= 16'b0;
        dstrans.W_Control <= 2'b0;
        dstrans.E_Control <= 6'b0;
        dsmbx.put(dstrans);
        
        $display("[DRV]: RESET DONE");
    endtask
    
    task decode();
        @(posedge vif.clk);
        vif.rst           <= 1'b0;
        vif.npc_in        <= gdtrans.npc_in;
        vif.enable_decode <= 1'b1;
        vif.Imem_dout     <= gdtrans.Imem_dout;
        
        @(posedge vif.clk);
        dstrans.IR        <= gdtrans.Imem_dout;
        dstrans.npc_out   <= gdtrans.npc_in;
        // Expected W_Control and E_Control will be determined in the scoreboard
        dsmbx.put(dstrans);
        
        $display("[DRV]: op: decode | npc_in: %0h | enable_decode: %0b | Imem_dout: %0b", vif.npc_in, vif.enable_decode, vif.Imem_dout);
    endtask
    
    task no_update();
        @(posedge vif.clk);
        vif.rst           <= 1'b0;
        vif.npc_in        <= gdtrans.npc_in;
        vif.enable_decode <= 1'b0;
        vif.Imem_dout     <= gdtrans.Imem_dout;
        
        @(posedge vif.clk);
        dstrans.IR        <= gdtrans.Imem_dout;
        dstrans.npc_out   <= gdtrans.npc_in;
        // Expected W_Control and E_Control will be determined in the scoreboard
        dsmbx.put(dstrans);
        $display("[DRV]: op: no_update | npc_in: %0h | enable_decode: %0b | Imem_dout: %0b", vif.npc_in, vif.enable_decode, vif.Imem_dout);
    endtask
    
    task run();
        forever begin
            gdmbx.get(gdtrans);
            if (gdtrans.op == op_pkg::reset) begin
                reset();
            end else if (gdtrans.op == op_pkg::decode) begin
                decode();
            end else if (gdtrans.op == op_pkg::no_update) begin
                no_update();
            end
            -> drvnext;
        end        
    endtask
endclass

/////////////////////////////////

class monitor;
    transaction trans;
    mailbox #(transaction) msmbx;
    virtual decode_if vif;
    
    function new (mailbox #(transaction) msmbx);
        trans = new();
        this.msmbx = msmbx;        
    endfunction
    
    task run();
        forever begin
            repeat (2) @(posedge vif.clk);
            trans.IR        = vif.IR;
            trans.npc_out   = vif.npc_out;
            trans.W_Control = vif.W_Control;
            trans.E_Control = vif.E_Control;
            @(posedge vif.clk);
            msmbx.put(trans);
            $display("[MON]: IR: %0b | npc_out: %0h | W_Control: %0b | E_Control: %0b", trans.IR, trans.npc_out, trans.W_Control, trans.E_Control);           
        end
    endtask
endclass

/////////////////////////////////

class scoreboard;
    transaction dstrans;
    transactoin mstrans;
    mailbox #(transaction) dsmbx;
    mailbox #(transaction) msmbx;
    
    byte E_Control_Valid;
    
    event sconext;
    
    function new (mailbox #(transaction) dsmbx, mailbox #(transaction) msmbx);
        this.dsmbx = dsmbx;
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin
            dsmbx.get(dstrans);
            msmbx.get(mstrans); 
            
            DecodeIR(dstrans.IR, dstrans.W_Control, dstrans.E_Control, E_Control_Valid);
            
            $display("[SCO-DRV]: IR: %0b | npc_out: %0h | W_Control: %0b | E_Control: %0b", dstrans.IR, dstrans.npc_out, dstrans.W_Control, dstrans.E_Control);
            $display("[SCO-MON]: IR: %0b | npc_out: %0h | W_Control: %0b | E_Control: %0b", mstrans.IR, mstrans.npc_out, mstrans.W_Control, mstrans.E_Control);
            
            if ( ( dstrans.W_Control == mstrans.W_Control ) && ( dstrans.E_Control & E_Control_Valid == mstrans.E_Control & E_Control_Valid ) )
                $display("DATA MATCH");
            else
                $display("DATA MISMATCH");
            $display("--------------------------");
            -> sconext;
        end
    endtask
endclass

/////////////////////////////////

    
module decode_tb;

endmodule