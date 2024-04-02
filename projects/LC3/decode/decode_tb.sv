`timescale 1ns / 1ps

`include "e_w_control_pkg.sv"

import e_w_control_pkg::*;

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

package decode_op_pkg;
    typedef enum { reset, decode, no_update} decode_op_t;
endpackage

import decode_op_pkg::*;

/////////////////////////////////

package opcode_pkg;
    typedef enum { add_op, and_op, not_op, lea_op } opcode_t;
endpackage

import opcode_pkg::*;

/////////////////////////////////

class transaction;
    rand decode_op_t        op;
    rand opcode_t           opcode;
    rand bit         [15:0] npc_in;
         bit                enable_decode;
    rand bit         [15:0] Imem_dout;
     
         bit         [15:0] IR;
         bit         [15:0] npc_out;
         logic       [1:0]  W_Control;
         logic       [5:0]  E_Control;
    
    function transaction copy();
        copy = new();
        copy.op            = this.op;
        copy.opcode        = this.opcode;
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
                  decode_op_pkg::reset     := 10, 
                  decode_op_pkg::decode    := 90,
                  decode_op_pkg::no_update := 10 
                };
    }
    
    constraint opcode_cntrl {
        opcode dist {
                      opcode_pkg::add_op := 25, 
                      opcode_pkg::and_op := 25,
                      opcode_pkg::not_op := 25,
                      opcode_pkg::lea_op := 25
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
            $display("[GEN]:     op: %0p | opcode: %0p | npc_in: %04h ", trans.op, trans.opcode, trans.npc_in);
            
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
        dstrans    = new();
        this.gdmbx = gdmbx;
        this.dsmbx = dsmbx;
    endfunction
    
    task global_reset();
        vif.rst           <= 1'b1;
        vif.npc_in        <= 16'b0;
        vif.enable_decode <= 1'b0;
        vif.Imem_dout     <= 16'b0;
        
        repeat(5) @(posedge vif.clk);
        vif.rst           <= 1'b0;
        
        $display("[DRV]: GLOBAL RESET DONE");
        $display("--------------------------");
        @(posedge vif.clk);
    endtask
    
    task reset();
        vif.rst           <= 1'b1;
        vif.npc_in        <= 16'b0;
        vif.enable_decode <= 1'b0;
        vif.Imem_dout     <= 16'b0;
        
        @(posedge vif.clk);
        vif.rst           <= 1'b0;
        dstrans.op        <= decode_op_pkg::reset;
        dstrans.IR        <= 16'b0;
        dstrans.npc_out   <= 16'b0;
        dstrans.W_Control <= 2'b0;
        dstrans.E_Control <= 6'b0;
        $display("[DRV]:     RESET DONE");
        @(posedge vif.clk);
        dsmbx.put(dstrans.copy());
    endtask
    
    task add_op();
        vif.Imem_dout[15:12] <= 4'b0001;
    endtask
    
    task and_op();
        vif.Imem_dout[15:12] <= 4'b0101;
    endtask
    
    task not_op();
        vif.Imem_dout[15:12] <= 4'b1001;
    endtask
    
    task lea_op();
        vif.Imem_dout[15:12] <= 4'b1110;
    endtask
    
    task decode();
        vif.rst           <= 1'b0;
        vif.npc_in        <= gdtrans.npc_in;
        vif.enable_decode <= 1'b1;
        vif.Imem_dout     <= gdtrans.Imem_dout;
        case (gdtrans.opcode)
            opcode_pkg::add_op: add_op();
            opcode_pkg::and_op: and_op();
            opcode_pkg::not_op: not_op();
            opcode_pkg::lea_op: lea_op();
        endcase                      
        
        @(posedge vif.clk);
        dstrans.op        <= decode_op_pkg::decode;
        dstrans.IR        <= vif.Imem_dout;
        dstrans.npc_out   <= vif.npc_in;  
        // Expected W_Control and E_Control will be determined in the scoreboard          
        $display("[DRV]:     op: decode | opcode: %0p | npc_in: %04h  | enable_decode: %0b | Imem_dout: %04h", gdtrans.opcode, vif.npc_in, vif.enable_decode, vif.Imem_dout);    
        @(posedge vif.clk);
        dsmbx.put(dstrans.copy());      
    endtask
    
    task no_update();  
        vif.rst           <= 1'b0;
        vif.npc_in        <= gdtrans.npc_in;
        vif.enable_decode <= 1'b0;
        vif.Imem_dout     <= gdtrans.Imem_dout;        
        
        @(posedge vif.clk);  
        dstrans.op        <= decode_op_pkg::no_update;
        dstrans.IR        <= gdtrans.Imem_dout;
        dstrans.npc_out   <= gdtrans.npc_in;                     
        $display("[DRV]:     op: no_update | npc_in: %04h | enable_decode: %0b | Imem_dout: %04h", vif.npc_in, vif.enable_decode, vif.Imem_dout);
        @(posedge vif.clk); 
        dsmbx.put(dstrans.copy());                       
    endtask
    
    task run();
        forever begin
            gdmbx.get(gdtrans);
            if (gdtrans.op == decode_op_pkg::reset) begin
                reset();
            end else if (gdtrans.op == decode_op_pkg::decode) begin
                decode();
            end else if (gdtrans.op == decode_op_pkg::no_update) begin
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
            msmbx.put(trans.copy());
            $display("[MON]:     IR: %04h   | npc_out: %04h  | W_Control: %02b | E_Control: %06b", trans.IR, trans.npc_out, trans.W_Control, trans.E_Control);           
        end
    endtask
endclass

/////////////////////////////////

class scoreboard;
    transaction dstrans;
    transaction mstrans;
    mailbox #(transaction) dsmbx;
    mailbox #(transaction) msmbx;
    
    logic [1:0] dstrans_w_control;
    logic [5:0] dstrans_e_control;
    
    event sconext;
    
    function new (mailbox #(transaction) dsmbx, mailbox #(transaction) msmbx);
        this.dsmbx = dsmbx;
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin
            dsmbx.get(dstrans);
            msmbx.get(mstrans); 
            
            dstrans_w_control = w_control(dstrans.IR);
            dstrans_e_control = e_control(dstrans.IR);
            
            if ( dstrans.op == decode_op_pkg::decode)
                $display("[SCO-DRV]: IR: %04h   | npc_out: %04h  | W_Control: %02b | E_Control: %06b", dstrans.IR, dstrans.npc_out, dstrans_w_control, dstrans_e_control);
            $display("[SCO-MON]: IR: %04h   | npc_out: %04h  | W_Control: %02b | E_Control: %06b", mstrans.IR, mstrans.npc_out, mstrans.W_Control, mstrans.E_Control);                      
            
            if ( dstrans.op == decode_op_pkg::decode) 
                if ( ( dstrans_w_control === mstrans.W_Control ) && ( dstrans_e_control === mstrans.E_Control ) )
                    $display("DATA MATCH");
                else
                    $display("DATA MISMATCH");
            $display("--------------------------");
            -> sconext;
        end
    endtask
endclass

/////////////////////////////////

class environment;    
    mailbox #(transaction) gdmbx;
    mailbox #(transaction) dsmbx;
    mailbox #(transaction) msmbx;
    
    virtual decode_if vif;
    
    event drvnext;
    event sconext;
    
    generator  gen;
    driver     drv;
    monitor    mon;
    scoreboard sco;
    
    function new(virtual decode_if vif);
        gdmbx       = new();
        dsmbx       = new();
        msmbx       = new();
        
        gen         = new(gdmbx);
        drv         = new(gdmbx, dsmbx);
        mon         = new(msmbx);
        sco         = new(dsmbx, msmbx);
                
        this.vif    = vif;
        drv.vif     = vif;
        mon.vif     = vif;

        gen.drvnext = drvnext;
        drv.drvnext = drvnext;
        gen.sconext = sconext;
        sco.sconext = sconext;
    endfunction
    
    task pre_test();
        drv.global_reset();
    endtask
    
    task test();
        fork
            gen.run();
            drv.run();
            mon.run();
            sco.run();
        join_any
    endtask
    
    task post_test();
        wait(gen.done.triggered());
        $finish;
    endtask
    
    task run();
        pre_test();
        test();
        post_test();
    endtask
endclass

/////////////////////////////////
    
module decode_tb;
   decode_if decode_vif();
   
   decode dut (
                .clk(decode_vif.clk), 
                .rst(decode_vif.rst),
                .npc_in(decode_vif.npc_in),
                .enable_decode(decode_vif.enable_decode),
                .Imem_dout(decode_vif.Imem_dout),
                .IR(decode_vif.IR),
                .npc_out(decode_vif.npc_out),
                .W_Control(decode_vif.W_Control),
                .E_Control(decode_vif.E_Control)
              );
              
    initial begin
        decode_vif.clk <= 0;
    end
    
    always #5 decode_vif.clk <= ~decode_vif.clk;
    
    environment env;
    
    initial begin
        env = new(decode_vif);
        env.gen.count = 20;
        env.run();
    end
    
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end
endmodule
