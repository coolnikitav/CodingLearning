`timescale 1ns / 1ps

interface alu_if;
    logic        clk;
    logic        rst;
    logic        enable;
    logic [1:0]  alu_control;
    logic [15:0] aluin1;
    logic [15:0] aluin2;
    logic [15:0] aluout;
endinterface

/////////////////////////////////

package op_pkg;
    typedef enum { rst_op, add_op, and_op, not_op, ne_op } op_t;
endpackage

import op_pkg::*;

/////////////////////////////////

class transaction_alu;
    rand op_t       op;
         bit        enable;
         bit [1:0]  alu_control;
    rand bit [15:0] aluin1;
    rand bit [15:0] aluin2;
         bit [15:0] aluout;
         
    function transaction_alu copy();
        copy             = new();
        copy.op          = this.op;
        copy.enable      = this.enable;
        copy.alu_control = this.alu_control;
        copy.aluin1      = this.aluin1;
        copy.aluin2      = this.aluin2;
        copy.aluout      = this.aluout;
    endfunction
    
    constraint op_cntrl {
        //op == op_pkg::add_op;
    }    
endclass

/////////////////////////////////

class generator_alu;
    transaction_alu gdtrans;
    mailbox #(transaction_alu) gdmbx;
    
    event drvnext;
    event sconext;
    event done;
    
    int count;
    
    function new (mailbox #(transaction_alu) gdmbx);
        this.gdmbx = gdmbx;
    endfunction
    
    task run();
        repeat (count) begin
            gdtrans = new();
            assert(gdtrans.randomize()) else $error("RANDOMIZATION FAILED");
            gdmbx.put(gdtrans.copy());
            $display("[GEN]: op: %0s | aluin1: %016b | aluin2: %016b", gdtrans.op, gdtrans.aluin1, gdtrans.aluin2);
            
            @(drvnext);
            @(sconext);            
        end
        -> done;
    endtask
endclass

/////////////////////////////////

class driver_alu;
    transaction_alu gdtrans;
    mailbox #(transaction_alu) gdmbx;
    mailbox #(bit [15:0])  dsmbx;
    
    virtual alu_if vif;
    
    event drvnext;
    
    function new (mailbox #(transaction_alu) gdmbx, mailbox #(bit [15:0]) dsmbx);        
        this.gdmbx = gdmbx;
        this.dsmbx = dsmbx;
    endfunction
    
    task rst_op();
        @(posedge vif.clk);
        vif.rst         <= 1'b1;
        @(posedge vif.clk);
        vif.rst         <= 1'b0;        
        dsmbx.put(16'h0);
        $display("[DRV]: op: rst_op");  
    endtask
    
    task add_op();        
        vif.rst         <= 1'b0;
        vif.enable      <= 1'b1;
        vif.alu_control <= 2'h0;
        vif.aluin1      <= gdtrans.aluin1;
        vif.aluin2      <= gdtrans.aluin2;        
        @(posedge vif.clk);
        dsmbx.put(gdtrans.aluin1 + gdtrans.aluin2);
        $display("[DRV]: op: add_op | aluin1: %016b | aluin2: %016b", gdtrans.aluin1, gdtrans.aluin2);
        @(posedge vif.clk);
    endtask
    
    task and_op();        
        vif.rst         <= 1'b0;
        vif.enable      <= 1'b1;
        vif.alu_control <= 2'h1;
        vif.aluin1      <= gdtrans.aluin1;
        vif.aluin2      <= gdtrans.aluin2;        
        @(posedge vif.clk);  
        dsmbx.put(gdtrans.aluin1 & gdtrans.aluin2);      
        $display("[DRV]: op: and_op | aluin1: %016b | aluin2: %016b", gdtrans.aluin1, gdtrans.aluin2);
        @(posedge vif.clk);
    endtask
    
    task not_op();

        vif.rst         <= 1'b0;
        vif.enable      <= 1'b1;
        vif.alu_control <= 2'h2;
        vif.aluin1      <= gdtrans.aluin1;        
        @(posedge vif.clk); 
        dsmbx.put(~gdtrans.aluin1);       
        $display("[DRV]: op: not_op | aluin1: %016b", gdtrans.aluin1);
        @(posedge vif.clk);
    endtask
    
    task ne_op();            
        vif.rst         <= 1'b0;
        vif.enable      <= 1'b0;        
        @(posedge vif.clk);
        dsmbx.put(vif.aluout);
        $display("[DRV]: op_op: ne");
        @(posedge vif.clk);
    endtask
    
    task run();
        forever begin
            gdmbx.get(gdtrans);
            case (gdtrans.op)
                op_pkg::rst_op: rst_op();
                op_pkg::add_op: add_op();
                op_pkg::and_op: and_op();
                op_pkg::not_op: not_op();
                op_pkg::ne_op:  ne_op();
            endcase
            -> drvnext;
        end       
    endtask
endclass

/////////////////////////////////

class monitor_alu;
    mailbox #(bit [15:0]) msmbx;
    
    virtual alu_if vif;
    
    function new (mailbox #(bit [15:0]) msmbx);        
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin
            repeat(2) @(posedge vif.clk);
            msmbx.put(vif.aluout);            
            @(posedge vif.clk);
            $display("[MON]: aluout: %016b | aluin1: %016b | aluin2: %016b", vif.aluout, vif.aluin1, vif.aluin2);
        end                
    endtask
endclass

/////////////////////////////////

class scoreboard_alu;
    mailbox #(bit [15:0]) dsmbx;
    mailbox #(bit [15:0]) msmbx;
    
    event sconext;
    
    bit [15:0] aluout_ref;
    bit [15:0] aluout;
    
    function new (mailbox #(bit [15:0])  dsmbx, mailbox #(bit [15:0]) msmbx);
        this.dsmbx = dsmbx;
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin           
            dsmbx.get(aluout_ref);
            msmbx.get(aluout);
            $display("[SCO]: aluout: %016b | aluout_ref: %016b", aluout, aluout_ref);
            
            if (aluout_ref == aluout)
                $display("DATA MATCH");
            else
                $display("DATA MISMATCH");   
            $display("------------------------");
            
            -> sconext;        
        end
    endtask
endclass

/////////////////////////////////

class environment_alu;
    mailbox #(transaction_alu) gdmbx;
    mailbox #(bit [15:0])  dsmbx;
    mailbox #(bit [15:0])  msmbx;
    
    event drvnext;
    event sconext;
    event done;
    
    virtual alu_if vif;
    
    generator_alu  gen;
    driver_alu     drv;
    monitor_alu    mon;
    scoreboard_alu sco;
    
    function new (virtual alu_if vif);
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
        //drv.rst_op();
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

/////////////////////////////////

module alu_tb;
    alu_if vif();
    
    alu dut (
        .clk(vif.clk),
        .rst(vif.rst),
        .enable(vif.enable),
        .alu_control(vif.alu_control),
        .aluin1(vif.aluin1),
        .aluin2(vif.aluin2),
        .aluout(vif.aluout) 
    );
    
    initial vif.clk <= 0;
    
    always #5 vif.clk <= ~vif.clk;
    
    environment_alu env;
    
    initial begin
        env = new(vif);
        env.gen.count = 20;
        env.run();
    end
endmodule
