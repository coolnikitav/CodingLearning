`timescale 1ns / 1ps

interface writeback_if;
    logic        clk;
    logic        rst;
    logic        enable_writeback;
    logic [15:0] aluout;
    logic [2:0]  W_Control;
    logic [15:0] pcout;
    logic [15:0] memout;
    logic [15:0] VSR1;
    logic [15:0] VSR2;
    logic [2:0]  dr;
    logic [2:0]  sr1;
    logic [2:0]  sr2;
endinterface

/////////////////////////////////

class transaction_wb;
    rand bit        enable_writeback;
    rand bit [15:0] aluout;
    rand bit [15:0] pcout;
    rand bit [15:0] memout;
    rand bit [1:0]  W_Control;
         bit [15:0] VSR1;
         bit [15:0] VSR2;
    rand bit [2:0]  dr;
    rand bit [2:0]  sr1;
    rand bit [2:0]  sr2;
         
    function transaction_wb copy();
        copy                  = new();
        copy.enable_writeback = this.enable_writeback;
        copy.aluout           = this.aluout;
        copy.pcout            = this.pcout;
        copy.memout           = this.memout;
        copy.W_Control        = this.W_Control;
        copy.VSR1             = this.VSR1;
        copy.VSR2             = this.VSR2;
        copy.dr               = this.dr;
        copy.sr1              = this.sr1;
        copy.sr2              = this.sr2;
    endfunction
    
    constraint en_cntrl {
        enable_writeback dist {
            1 := 90,
            0 := 10
        };
    }
    
    constraint W_Control_cntrl {
        W_Control dist {
            0 := 70,
            2 := 30
        };
    }
endclass

/////////////////////////////////

class generator_wb;
    transaction_wb gdtrans;
    mailbox #(transaction_wb) gdmbx;
    
    event drvnext;
    event sconext;
    event done;
    
    int count = 0;
    
    function new (mailbox #(transaction_wb) gdmbx);
        this.gdmbx = gdmbx;
    endfunction
    
    task run();
        repeat (count) begin
            gdtrans = new();
            assert (gdtrans.randomize()) else $error("RANDOMIZATION FAILED");
            gdmbx.put(gdtrans.copy());
            $display("[GEN]: en: %0b | aluout: %04h | pcout: %04h | memout: %04h | W_Control: %01h | dr: %01h | sr1: %01h | sr2: %01h", gdtrans.enable_writeback, gdtrans.aluout, gdtrans.pcout, gdtrans.memout, gdtrans.W_Control, gdtrans.dr, gdtrans.sr1, gdtrans.sr2);
            @(drvnext);
            @(sconext);
        end 
        -> done;    
    endtask
endclass

/////////////////////////////////

class driver_wb;
    transaction_wb gdtrans;
    transaction_wb dstrans;
    mailbox #(transaction_wb) gdmbx;
    mailbox #(transaction_wb) dsmbx;
    
    virtual writeback_if vif;
    
    event drvnext;
    
    reg [15:0] register_files [7:0];
        
    function new (mailbox #(transaction_wb) gdmbx,mailbox #(transaction_wb) dsmbx);
        this.gdmbx = gdmbx;
        this.dsmbx = dsmbx;
    endfunction
    
    task reset();
        vif.rst              <= 1'b1;
        for (int i = 0; i < 8; i++) begin
            register_files[i] = 16'h0;          
        end
        @(posedge vif.clk);
        vif.rst              <= 1'b0;
        $display("[DRV]: RESET DONE");
        $display("--------------------------------");
    endtask    
    
    task run();        
        forever begin
            gdmbx.get(gdtrans);
            
            vif.rst              <= 1'b0;
            vif.enable_writeback <= gdtrans.enable_writeback;
            vif.aluout           <= gdtrans.aluout;
            vif.pcout            <= gdtrans.pcout;
            vif.memout           <= gdtrans.memout;
            vif.W_Control        <= gdtrans.W_Control;
            vif.dr               <= gdtrans.dr;
            vif.sr1              <= gdtrans.sr1;
            vif.sr2              <= gdtrans.sr2;
            
            if (gdtrans.enable_writeback == 1'b1) begin
                register_files[gdtrans.dr] = gdtrans.W_Control == 0 ? gdtrans.aluout : gdtrans.pcout; 
                $display("[DRV]: MODULE ENABLED");
            end
                                            
            @(posedge vif.clk);
            dstrans = new();
            dstrans.VSR1 = register_files[gdtrans.sr1];
            dstrans.VSR2 = register_files[gdtrans.sr2];
            dsmbx.put(dstrans);                        
                
            -> drvnext; 
        end
    endtask
endclass

/////////////////////////////////

class monitor_wb;
    transaction_wb mstrans;
    mailbox #(transaction_wb) msmbx;
    
    virtual writeback_if vif;
    
    function new(mailbox #(transaction_wb) msmbx);
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin
            repeat(2) @(posedge vif.clk);
            mstrans = new();
            mstrans.VSR1 = vif.VSR1;
            mstrans.VSR2 = vif.VSR2;
            msmbx.put(mstrans);
            $display("[MON]:     VSR1: %04h | VSR2: %04h", mstrans.VSR1, mstrans.VSR2);
        end
    endtask
endclass

/////////////////////////////////

class scoreboard_wb;
    transaction_wb dstrans;
    transaction_wb mstrans;
    mailbox #(transaction_wb) dsmbx;
    mailbox #(transaction_wb) msmbx;
    
    event sconext;
    
    function new (mailbox #(transaction_wb) dsmbx, mailbox #(transaction_wb) msmbx);
        this.dsmbx = dsmbx;
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin
            dsmbx.get(dstrans);
            msmbx.get(mstrans);
            
            $display("[SCO-DRV]: VSR1: %04h | VSR2: %04h", dstrans.VSR1, dstrans.VSR2);
            $display("[SCO-MON]: VSR1: %04h | VSR2: %04h", mstrans.VSR1, mstrans.VSR2);
            
            if (dstrans.VSR1 == mstrans.VSR1 && dstrans.VSR2 == mstrans.VSR2)
                $display("[SCO]: DATA MATCH");
            else
                $display("[SCO]: DATA MISMATCH");
            $display("--------------------------------");
            -> sconext;
        end
    endtask
endclass

/////////////////////////////////

class environment_wb;
    mailbox #(transaction_wb) gdmbx;
    mailbox #(transaction_wb) dsmbx;
    mailbox #(transaction_wb) msmbx;
    
    virtual writeback_if vif;
    
    event drvnext;
    event sconext;
    event done;
    
    generator_wb  gen;
    driver_wb     drv;
    monitor_wb    mon;
    scoreboard_wb sco;
    
    function new (virtual writeback_if vif);
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

module writeback_tb;
    writeback_if vif();
    
    writeback dut(
        .clk(vif.clk),
        .rst(vif.rst),
        .enable_writeback(vif.enable_writeback),
        .aluout(vif.aluout),
        .W_Control(vif.W_Control),
        .pcout(vif.pcout),
        .memout(vif.memout),
        .VSR1(vif.VSR1),
        .VSR2(vif.VSR2),
        .dr(vif.dr),
        .sr1(vif.sr1),
        .sr2(vif.sr2)
    );
    
    initial vif.clk <= 0;
    always #5 vif.clk <= ~vif.clk;
    
    environment_wb env;
    
    initial begin
        env = new(vif);
        env.gen.count = 30;
        env.run();
    end
endmodule
