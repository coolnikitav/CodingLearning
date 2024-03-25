`timescale 1ns / 1ps

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

class transaction;
    rand bit [15:0] npc_in;
    rand bit        enable_decode;
    rand bit [15:0] Imem_dout;
     
         bit [15:0] IR;
         bit [15:0] npc_out;
         bit [1:0]  W_Control;
         bit [5:0]  E_Control;
    
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
    
    constraint enable_decode_cntrl {
        enable_decode dist { 1 := 90, 0 := 10 };
    }
endclass

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
            $display("[GEN]: npc_in: %0h | enable_decode: %0b | Imem_rd: %0h", trans.npc_in, trans.enable_decode, trans.Imem_rd);
            
            gdmbx.put(trans.copy());
            
            @(drvnext);
            @(sconext);
        end
        -> done;
    endtask
endclass

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
        vif.enable_decode <= gdrans.enable_decode;
        vif.Imem_dout     <= gdtrans.Imem_dout;
        
        @(posedge vif.clk);
        dstrans.IR        <= gdtrans.Imem_dout;
        dstrans.npc_out   <= gdtrans.npc_in;
        dstrans.W_Control <= 2'b0;
        dstrans.E_Control <= 6'b0;
        dsmbx.put(dstrans);
    endtask
endclass
    
module decode_tb;

endmodule
