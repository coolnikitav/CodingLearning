`timescale 1ns / 1ps

interface extension_if;
    logic [15:0] IR;
    logic [15:0] imm5;
    logic [15:0] offset6;
    logic [15:0] offset9;
    logic [15:0] offset11;
endinterface

/*
 *  Extension module does not have a clock,
 *  but execute does
 */
interface clk_if;
    logic clk;    
    
    initial clk <= 0;
    
    always #5 clk = ~clk;
endinterface

/////////////////////////////////

class transaction;
    rand bit [15:0] IR;
         bit [15:0] imm5;
         bit [15:0] offset6;
         bit [15:0] offset9;
         bit [15:0] offset11;
         
    function transaction copy();
        copy          = new();
        copy.IR       = this.IR;
        copy.imm5     = this.imm5;
        copy.offset6  = this.offset6;
        copy.offset9  = this.offset9;
        copy.offset11 = this.offset11;
    endfunction       
endclass

/////////////////////////////////

class generator;
    transaction trans;
    mailbox #(transaction) gdmbx;
    
    event drvnext;
    event sconext;
    event done;
    
    int count = 0;
    
    function new (mailbox #(transaction) gdmbx);
        this.gdmbx = gdmbx;
    endfunction
    
    task run();
        repeat(count) begin
            trans = new();
            assert (trans.randomize()) else $error("RANDOMIZATION FAILED");
            gdmbx.put(trans.copy());
            $display("[GEN]:       IR: %016b |      IR: %016b |      IR: %016b |       IR: %016b", trans.IR, trans.IR, trans.IR, trans.IR);
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
    mailbox #(transaction) gdmbx;
    mailbox #(transaction) dsmbx;
    
    virtual clk_if tb_clk;
    virtual extension_if vif;
    
    event drvnext;
    
    function new (mailbox #(transaction) gdmbx, mailbox #(transaction) dsmbx);
        dstrans    = new();
        this.gdmbx = gdmbx;
        this.dsmbx = dsmbx;
    endfunction
    
    task run();
        forever begin
            @(posedge tb_clk.clk);
            gdmbx.get(gdtrans);
            vif.IR = gdtrans.IR;

            dstrans.IR       = gdtrans.IR;
            dstrans.imm5     = { {11{gdtrans.IR[4]}},  gdtrans.IR[4:0]  };
            dstrans.offset6  = { {10{gdtrans.IR[5]}},  gdtrans.IR[5:0]  };
            dstrans.offset9  = {  {7{gdtrans.IR[8]}},  gdtrans.IR[8:0]  };
            dstrans.offset11 = {  {5{gdtrans.IR[10]}}, gdtrans.IR[10:0] };
            dsmbx.put(dstrans);
            
            -> drvnext;
        end
    endtask
endclass

/////////////////////////////////

class monitor;
    transaction trans;
    mailbox #(transaction) msmbx;
    
    virtual clk_if tb_clk;
    virtual extension_if vif;
    
    function new (mailbox #(transaction) msmbx);
        trans      = new();
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin
            repeat(2) @(posedge tb_clk.clk);
            trans.imm5     = vif.imm5;
            trans.offset6  = vif.offset6;
            trans.offset9  = vif.offset9;
            trans.offset11 = vif.offset11;
            msmbx.put(trans.copy());          
            $display("[MON]:     imm5: %016b | offset6: %016b | offset9: %016b | offset11: %016b", vif.imm5, vif.offset6, vif.offset9, vif.offset11);            
        end
    endtask
endclass

/////////////////////////////////

class scoreboard;
    transaction dstrans;
    transaction mstrans;
    mailbox #(transaction) dsmbx;
    mailbox #(transaction) msmbx;

    event sconext;
    
    function new (mailbox #(transaction) dsmbx, mailbox #(transaction) msmbx);
        this.dsmbx = dsmbx;
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin
            dsmbx.get(dstrans);
            msmbx.get(mstrans);
            
            $display("[SCO-DRV]: imm5: %016b | offset6: %016b | offset9: %016b | offset11: %016b", dstrans.imm5, dstrans.offset6, dstrans.offset9, dstrans.offset11);
            $display("[SCO-MON]: imm5: %016b | offset6: %016b | offset9: %016b | offset11: %016b", mstrans.imm5, mstrans.offset6, mstrans.offset9, mstrans.offset11);
        
            if (dstrans.imm5 == mstrans.imm5 && dstrans.offset6 == mstrans.offset6 && dstrans.offset9 == mstrans.offset9 &&  dstrans.offset11 == mstrans.offset11)
                $display("[SCO]:                                              DATA MATCH");
            else
                $display("[SCO]:                                             DATA MISMATCH");           
            $display("----------------------------------------------------------------------------------------------------------------------");
            -> sconext;
        end
    endtask
endclass

/////////////////////////////////

class environment;
    mailbox #(transaction) gdmbx;
    mailbox #(transaction) dsmbx;
    mailbox #(transaction) msmbx;
    
    virtual clk_if tb_clk;
    virtual extension_if vif;
    
    event drvnext;
    event sconext;
    
    generator  gen;
    driver     drv;
    monitor    mon;
    scoreboard sco;
    
    function new (virtual clk_if tb_clk, virtual extension_if vif);
        gdmbx       = new();
        dsmbx       = new();
        msmbx       = new();
        
        gen         = new(gdmbx);
        drv         = new(gdmbx, dsmbx);
        mon         = new(msmbx);
        sco         = new(dsmbx, msmbx);
        
        this.tb_clk = tb_clk;
        drv.tb_clk  = tb_clk;
        mon.tb_clk  = tb_clk;
                
        this.vif    = vif;
        drv.vif     = vif;
        mon.vif     = vif;
        
        gen.drvnext = drvnext; 
        drv.drvnext = drvnext;
        gen.sconext = sconext; 
        sco.sconext = sconext;
    endfunction
    
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
        test();
        post_test();
    endtask
endclass

/////////////////////////////////

module extension_tb;
    clk_if tb_clk();   
    
    extension_if extension_vif();
    
    extension dut (
        .IR(extension_vif.IR),
        .imm5(extension_vif.imm5),
        .offset6(extension_vif.offset6),
        .offset9(extension_vif.offset9),
        .offset11(extension_vif.offset11)
        );
        
    environment env;
    
    initial begin
        env = new(tb_clk, extension_vif);
        env.gen.count = 20;
        env.run();
    end
endmodule
