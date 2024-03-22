`timescale 1ns / 1ps

interface fetch_if;
    logic        clk, rst;
    logic        enable_updatePC, enable_fetch;
    logic [15:0] taddr;
    logic        br_taken;
    logic [15:0] pc, npc;
    logic        Imem_rd;
endinterface

///////////////////////

package op_pkg;
    typedef enum { ball, update_br_taken, update_br_nt_taken, no_update, reset } op_t;
endpackage

import op_pkg::*;

///////////////////////

class transaction;
    rand op_t       op;
         bit        enable_updatePC, enable_fetch;    
    rand bit [15:0] taddr;
         bit        br_taken;
         bit [15:0] pc, npc;
         logic      Imem_rd;  // must be able to hold a Z value
         
    function transaction copy();
        copy                 = new();
        copy.op              = this.op;
        copy.enable_updatePC = this.enable_updatePC;
        copy.enable_fetch    = this.enable_fetch;
        copy.taddr           = this.taddr;
        copy.br_taken        = this.br_taken;
        copy.pc              = this.pc;
        copy.npc             = this.npc;
        copy.Imem_rd         = this.Imem_rd;
    endfunction
            
    constraint op_cntrl {
        op dist { 
                  op_pkg::update_br_taken := 4,
                  op_pkg::update_br_nt_taken := 4,
                  op_pkg::no_update := 2,
                  op_pkg::reset := 1
                };
    }
endclass

///////////////////////

class generator;
    transaction trans;
    mailbox #(transaction) gdmbx;  // gen -> drv
    
    int count = 0;
    
    event drvnext;
    event sconext;
    event done;
    
    function new (mailbox #(transaction) gdmbx);
        trans = new();
        this.gdmbx = gdmbx;
    endfunction  
    
    task run();
        repeat (count) begin
            assert(trans.randomize()) else $error("RANDOMIZATION FAILED");
            
            gdmbx.put(trans.copy());
            
            $display("[GEN]: op: %0s | taddr: %0h", trans.op, trans.taddr);
            
            @drvnext;
            @sconext;            
        end
        -> done;
    endtask  
endclass

///////////////////////

class driver;
    transaction gdtrans;
    transaction dstrans;
    mailbox #(transaction) gdmbx;  // gen -> drv
    mailbox #(transaction) dsmbx;  // drv -> sco
    virtual fetch_if vif;
    
    event drvnext;
    
    function new (mailbox #(transaction) gdmbx, mailbox #(transaction) dsmbx);
        dstrans = new();
        this.gdmbx = gdmbx;
        this.dsmbx = dsmbx;
    endfunction
    
    task reset();
        vif.rst             <= 1'b1;
        vif.enable_updatePC <= 1'b0;
        vif.enable_fetch    <= 1'bz;
        vif.taddr           <= 1'b0;
        vif.br_taken        <= 1'b0;
        @(posedge vif.clk);
        vif.rst             <= 1'b0;
        
        dstrans.pc          <= 16'h3000;
        dstrans.npc         <= 16'h3001;
        dstrans.Imem_rd     <= 1'bz;
        dsmbx.put(dstrans);
        
        $display("[DRV]: RESET DONE");
        @(posedge vif.clk);
    endtask
    
    task update_br_taken();
        vif.rst             <= 1'b0;
        vif.enable_updatePC <= 1'b1;
        vif.enable_fetch    <= 1'b1;
        vif.br_taken        <= 1'b1;
        vif.taddr           <= gdtrans.taddr;
        @(posedge vif.clk);
        vif.enable_updatePC <= 1'b0;
        
        dstrans.pc          <= gdtrans.taddr;
        dstrans.npc         <= gdtrans.taddr + 1;
        dstrans.Imem_rd     <= 1'b1;
        dsmbx.put(dstrans);
        
        $display("[DRV]: Branch taken, taddr: %0h", vif.taddr);
        @(posedge vif.clk);
    endtask
    
    task update_br_nt_taken();
        vif.rst             <= 1'b0;
        vif.enable_updatePC <= 1'b1;
        vif.enable_fetch    <= 1'b1;
        vif.br_taken        <= 1'b0;
        @(posedge vif.clk);
        vif.enable_updatePC <= 1'b0;
        
        @(posedge vif.clk);
        dstrans.pc          <= vif.pc;
        dstrans.npc         <= vif.pc+1;
        dstrans.Imem_rd     <= 1'b1;
        dsmbx.put(dstrans);
                
        $display("[DRV]: Branch not taken");
    endtask
    
    task no_update();
        vif.rst             <= 1'b0;
        vif.enable_updatePC <= 1'b0;
        vif.enable_fetch    <= 1'b0;
        @(posedge vif.clk);
        
        dstrans.pc          <= vif.pc;
        dstrans.npc         <= vif.pc+1;
        dstrans.Imem_rd     <= 1'bz;
        dsmbx.put(dstrans);
        
        $display("[DRV]: No update");
        @(posedge vif.clk);
    endtask
    
    task run();
        forever begin
            gdmbx.get(gdtrans);
            if (gdtrans.op == op_pkg::update_br_taken) begin
                update_br_taken(); 
            end else if (gdtrans.op == op_pkg::update_br_nt_taken) begin
                update_br_nt_taken();
            end else if (gdtrans.op == op_pkg::no_update) begin
                no_update();
            end else if (gdtrans.op == op_pkg::reset) begin
                reset();
            end
            -> drvnext;
        end
    endtask
endclass

///////////////////////

class monitor;
    transaction trans;
    mailbox #(transaction) msmbx;  // mon -> sco
    virtual fetch_if vif;
    
    function new (mailbox #(transaction) msmbx);
        trans = new();
        this.msmbx = msmbx;
    endfunction
    
    task run();
       forever begin
        repeat (2) @(posedge vif.clk);
        trans.pc      = vif.pc;
        trans.npc     = vif.npc;
        trans.Imem_rd = vif.Imem_rd;
        @(posedge vif.clk);
        msmbx.put(trans);
        $display("[MON]: pc: %0h | npc: %0h | Imem_rd: %0b", trans.pc, trans.npc, trans.Imem_rd);
       end
    endtask
endclass

///////////////////////

class scoreboard;
    transaction dstrans;
    transaction mstrans;
    mailbox #(transaction) dsmbx;  // drv -> sco
    mailbox #(transaction) msmbx;  // mon -> sco
    
    event sconext;
    
    function new (mailbox #(transaction) dsmbx, mailbox #(transaction) msmbx);
        dstrans = new();
        mstrans = new();
        this.dsmbx = dsmbx;
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin
          dsmbx.get(dstrans);
          msmbx.get(mstrans);
          
          $display("[SCO]: DRV: pc: %0h, npc: %0h, Imem_rd: %0b | MON: pc: %0h, npc: %0h, Imem_rd: %0b", dstrans.pc, dstrans.npc, dstrans.Imem_rd, mstrans.pc, mstrans.npc, mstrans.Imem_rd);
          
          if (dstrans.pc == mstrans.pc && dstrans.npc == mstrans.npc && dstrans.Imem_rd === mstrans.Imem_rd)  // need === to compare Z values
            $display("[SCO]: DATA MATCH");
          else
            $error("[SCO]: DATA MISMATCH"); 
          $display("--------------------------");
          -> sconext;
        end
    endtask
endclass

///////////////////////

class environment;
    generator gen;
    driver drv;
    monitor mon;
    scoreboard sco;
    
    mailbox #(transaction) gdmbx;
    mailbox #(transaction) dsmbx;
    mailbox #(transaction) msmbx;
    
    virtual fetch_if vif;
    
    event drvnext;
    event sconext;
    event done;
    
    function new(virtual fetch_if vif);
        gdmbx = new();
        dsmbx = new();
        msmbx = new();
        
        gen = new(gdmbx);
        drv = new(gdmbx, dsmbx);
        mon = new(msmbx);
        sco = new(dsmbx, msmbx); 
        
        this.vif = vif;
        drv.vif  = vif;
        mon.vif  = vif;
        
        gen.drvnext = drvnext;
        drv.drvnext = drvnext;
        gen.sconext = sconext;
        sco.sconext = sconext;
    endfunction
    
    task pre_test();
        drv.reset();
        $display("--------------------------");
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
        wait(gen.done.triggered);
        $finish;
    endtask
    
    task run();
        pre_test();
        test();
        post_test();
    endtask
endclass

///////////////////////

module fetch_tb;
    fetch_if vif();
    fetch dut 
    (
      .clk(vif.clk),
      .rst(vif.rst),
      .enable_updatePC(vif.enable_updatePC),
      .enable_fetch(vif.enable_fetch),
      .taddr(vif.taddr),
      .br_taken(vif.br_taken),
      .pc(vif.pc),
      .npc(vif.npc),
      .Imem_rd(vif.Imem_rd)
     );
         
    initial begin
        vif.clk <= 0;
    end
    
    always #5 vif.clk <= ~vif.clk;  // 100 MHz
    
    environment env;
    
    initial begin
        env = new(vif);
        env.gen.count = 50;
        env.run();
    end
    
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars;
    end
endmodule
