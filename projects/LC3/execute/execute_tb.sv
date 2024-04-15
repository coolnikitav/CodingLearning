`timescale 1ns / 1ns

interface execute_if;    
    logic        clk;
    logic        rst;
    logic        enable_execute;
    logic [5:0]  E_control;
    logic [15:0] IR;
    logic [15:0] npc_in;
    logic [1:0]  W_control_in;
    logic [15:0] aluout;
    logic [1:0]  W_control_out;
    logic [15:0] VSR1;
    logic [15:0] VSR2;
    logic [2:0]  dr;
    logic [2:0]  sr1;
    logic [2:0]  sr2;
    logic [15:0] pcout;
endinterface

/////////////////////////////////

package op_pkg;
    typedef enum { rst_op, add_reg_op, add_imm_op, and_reg_op, and_imm_op, not_op, lea_op, ne_op } op_t;    
endpackage

import op_pkg::*;

/////////////////////////////////

class transaction_exe;
    rand op_t       op;
         bit        enable_execute;
         bit        E_control;
    rand bit [15:0] IR;
    rand bit [15:0] npc_in;
         bit [1:0]  W_control_in;
         bit [15:0] aluout;
         bit [1:0]  W_control_out;
         bit [15:0] VSR1;
         bit [15:0] VSR2;
         bit [2:0]  dr;
         bit [2:0]  sr1;
         bit [2:0]  sr2;
         bit [15:0] pcout;
         
    function transaction_exe copy();
        copy                = new();
        copy.op             = this.op;
        copy.enable_execute = this.enable_execute;
        copy.E_control      = this.E_control;
        copy.IR             = this.IR;
        copy.npc_in         = this.npc_in;
        copy.W_control_in   = this.W_control_in;
        copy.aluout         = this.aluout;
        copy.W_control_out  = this.W_control_out;
        copy.VSR1           = this.VSR1;
        copy.VSR2           = this.VSR2;
        copy.dr             = this.dr;
        copy.sr1            = this.sr1;
        copy.sr2            = this.sr2;
        copy.pcout          = this.pcout;
    endfunction
endclass

/////////////////////////////////

class generator_exe;
    transaction_exe gdtrans;
    mailbox #(transaction_exe) gdmbx;
    
    event drvnext;
    event sconext;
    event done;
    
    int count;
    
    function new (mailbox #(transaction_exe) gdmbx);
        this.gdmbx = gdmbx;
    endfunction
    
    task run();
        repeat(count) begin
            gdtrans = new();   
            assert(gdtrans.randomize()) else $error("RANDOMIZATION FAILED");
            gdmbx.put(gdtrans.copy());
            $display("[GEN]:     [%0g]: op: %0p | IR: %016b | npc_in: %04h", $time, gdtrans.op, gdtrans.IR, gdtrans.npc_in);
                        
            @(drvnext);
            @(sconext);            
        end
        -> done;
    endtask
endclass

/////////////////////////////////

class driver_exe;
    transaction_exe gdtrans;
    transaction_exe dstrans;
    mailbox #(transaction_exe) gdmbx;
    mailbox #(transaction_exe) dsmbx;
    
    virtual execute_if vif;
    
    event drvnext;
    
    function new(mailbox #(transaction_exe) gdmbx, mailbox #(transaction_exe) dsmbx);
        dstrans    = new();
        this.gdmbx = gdmbx;
        this.dsmbx = dsmbx;
    endfunction
    
    task rst_op();
        vif.rst               <= 1'b1;
        @(posedge vif.clk);
        vif.rst               <= 1'b0;
        dstrans.op             = gdtrans.op;
        dstrans.aluout         = 16'h0;
        dstrans.pcout          = 16'h0;
        dstrans.W_control_out  = 2'h0;
        dstrans.dr             = 3'h0;
    endtask
    
    task add_reg_op();
        vif.rst               <= 1'b0;
        vif.enable_execute    <= 1'b1;
        vif.E_control         <= 6'b000001;
        vif.IR                <= { 4'b0001, gdtrans.IR[11:6], 1'b0, gdtrans.IR[4:0] };
        vif.npc_in            <= gdtrans.npc_in;
        vif.W_control_in      <= 2'h0;
        vif.VSR1               = gdtrans.IR[8:6];
        vif.VSR2               = gdtrans.IR[2:0];
        @(posedge vif.clk);
        dstrans.op             = gdtrans.op;
        dstrans.aluout         = vif.VSR1 + vif.VSR2;        
        dstrans.W_control_out  = 2'h0;
        dstrans.dr             = vif.IR[11:9];
        dstrans.sr1            = vif.IR[8:6];
        dstrans.sr2            = vif.IR[2:0];
        dstrans.pcout          = { {5{vif.IR[10]}}, vif.IR[10:0] } + vif.VSR1;  // pcselect1 = 0, pcselect2 = 0
    endtask
    
    task add_imm_op();
        vif.rst               <= 1'b0;
        vif.enable_execute    <= 1'b1;
        vif.E_control         <= 6'b000000;
        vif.IR                <= { 4'b0001, gdtrans.IR[11:6], 1'b1, gdtrans.IR[4:0] };
        vif.npc_in            <= gdtrans.npc_in;
        vif.W_control_in      <= 2'h0;
        vif.VSR1               = gdtrans.IR[8:6];     
        @(posedge vif.clk); 
        dstrans.op             = gdtrans.op;
        dstrans.aluout         = vif.VSR1 + { {11{vif.IR[4]}}, vif.IR[4:0] };        
        dstrans.W_control_out  = 2'h0;
        dstrans.dr             = vif.IR[11:9];
        dstrans.sr1            = vif.IR[8:6];
        dstrans.sr2            = vif.IR[2:0];
        dstrans.pcout          = { {5{vif.IR[10]}}, vif.IR[10:0] } + vif.VSR1;  // pcselect1 = 0, pcselect2 = 0
    endtask
    
    task and_reg_op();
        vif.rst               <= 1'b0;
        vif.enable_execute    <= 1'b1;
        vif.E_control         <= 6'b010001;
        vif.IR                <= { 4'b0101, gdtrans.IR[11:6], 1'b0, gdtrans.IR[4:0] };
        vif.npc_in            <= gdtrans.npc_in;
        vif.W_control_in      <= 2'h0;
        vif.VSR1               = gdtrans.IR[8:6];
        vif.VSR2               = gdtrans.IR[2:0];
        @(posedge vif.clk);
        dstrans.op             = gdtrans.op;
        dstrans.aluout         = vif.VSR1 & vif.VSR2;        
        dstrans.W_control_out  = 2'h0;
        dstrans.dr             = vif.IR[11:9];
        dstrans.sr1            = vif.IR[8:6];
        dstrans.sr2            = vif.IR[2:0];
        dstrans.pcout          = { {5{vif.IR[10]}}, vif.IR[10:0] } + vif.VSR1;  // pcselect1 = 0, pcselect2 = 0
    endtask
    
    task and_imm_op();
        vif.rst               <= 1'b0;
        vif.enable_execute    <= 1'b1;
        vif.E_control         <= 6'b010000;
        vif.IR                <= { 4'b0101, gdtrans.IR[11:6], 1'b1, gdtrans.IR[4:0] };
        vif.npc_in            <= gdtrans.npc_in;
        vif.W_control_in      <= 2'h0;
        vif.VSR1               = gdtrans.IR[8:6];
        @(posedge vif.clk);
        dstrans.op             = gdtrans.op;
        dstrans.aluout         = vif.VSR1 & { {11{vif.IR[4]}}, vif.IR[4:0] };        
        dstrans.W_control_out  = 2'h0;
        dstrans.dr             = vif.IR[11:9];
        dstrans.sr1            = vif.IR[8:6];
        dstrans.sr2            = vif.IR[2:0];
        dstrans.pcout          = { {5{vif.IR[10]}}, vif.IR[10:0] } + vif.VSR1;  // pcselect1 = 0, pcselect2 = 0
    endtask
    
    task not_op();
        vif.rst               <= 1'b0;
        vif.enable_execute    <= 1'b1;
        vif.E_control         <= 6'b100000;
        vif.IR                <= { 4'b1001, gdtrans.IR[11:0] };
        vif.npc_in            <= gdtrans.npc_in;
        vif.W_control_in      <= 2'h0;
        vif.VSR1               = gdtrans.IR[8:6];
        @(posedge vif.clk);
        dstrans.op             = gdtrans.op;
        dstrans.aluout         = ~vif.VSR1;        
        dstrans.W_control_out  = 2'h0;
        dstrans.dr             = vif.IR[11:9];
        dstrans.sr1            = vif.IR[8:6];
        dstrans.sr2            = vif.IR[2:0];
        dstrans.pcout          = { {5{vif.IR[10]}}, vif.IR[10:0] } + vif.VSR1;  // pcselect1 = 0, pcselect2 = 0
    endtask
    
    task lea_op();
        vif.rst               <= 1'b0;
        vif.enable_execute    <= 1'b1;
        vif.E_control         <= 6'b000110;
        vif.IR                <= { 4'b1110, gdtrans.IR[11:0] };
        vif.npc_in            <= gdtrans.npc_in;
        vif.W_control_in      <= 2'h2;
        @(posedge vif.clk);
        dstrans.op             = gdtrans.op;
        dstrans.W_control_out  = 2'h2;
        dstrans.dr             = vif.IR[11:9];
        dstrans.sr1            = vif.IR[8:6];
        dstrans.sr2            = vif.IR[2:0];
        dstrans.pcout          = { {7{vif.IR[8]}},  vif.IR[8:0] } + gdtrans.npc_in;  // pcselect1 = 1, pcselect2 = 1
    endtask
    
    task ne_op();
        vif.rst               <= 1'b0;
        vif.enable_execute    <= 1'b0;
        vif.npc_in            <= gdtrans.npc_in;
        @(posedge vif.clk);
        dstrans.op             = gdtrans.op;
        dstrans.aluout         = vif.aluout;        
        dstrans.W_control_out  = vif.W_control_out;
        dstrans.dr             = vif.dr;
        dstrans.sr1            = vif.sr1;
        dstrans.sr2            = vif.sr2;
        dstrans.pcout          = vif.pcout;
    endtask
    
    task run();
        forever begin
            gdmbx.get(gdtrans);
            
            case(gdtrans.op)
                op_pkg::rst_op:     rst_op();
                op_pkg::add_reg_op: add_reg_op();
                op_pkg::add_imm_op: add_imm_op();
                op_pkg::and_reg_op: and_reg_op();
                op_pkg::and_imm_op: and_imm_op();
                op_pkg::not_op:     not_op();
                op_pkg::lea_op:     lea_op();
                op_pkg::ne_op:      ne_op();
            endcase
                        
            dsmbx.put(dstrans.copy());
            $display("[DRV]:     [%0g]: op: %p | rst: %0b | enable_execute: %0b | E_control: %06b | IR: %016b | VSR1: %03b | VSR2: %03b | imm5: %016b | W_control_in: %02b", $time, gdtrans.op, vif.rst, vif.enable_execute, vif.E_control, vif.IR, gdtrans.IR[8:6], gdtrans.IR[2:0], { {11{gdtrans.IR[4]}}, gdtrans.IR[4:0] }, vif.W_control_in);
            
            -> drvnext;
        end
    endtask
endclass

/////////////////////////////////

class monitor_exe;
    transaction_exe mstrans;
    mailbox #(transaction_exe) msmbx;
    
    virtual execute_if vif;
    
    function new (mailbox #(transaction_exe) msmbx);
        this.msmbx = msmbx;
    endfunction
    
    task run();
        forever begin
            mstrans = new();
            repeat(2) @(posedge vif.clk);
            mstrans.aluout        = vif.aluout;        
            mstrans.W_control_out = vif.W_control_out;
            mstrans.dr            = vif.dr;
            mstrans.sr1           = vif.sr1;
            mstrans.sr2           = vif.sr2;
            mstrans.pcout         = vif.pcout; 
            msmbx.put(mstrans);
            $display("[MON]:     [%0g]: aluout: %04h | W_control_out: %02h | dr: %03b | sr1: %03b | sr2: %03b | pcout: %04h", $time, mstrans.aluout, mstrans.W_control_out, mstrans.dr, mstrans.sr1, mstrans.sr2, mstrans.pcout);
        end        
    endtask
endclass

/////////////////////////////////

class scoreboard_exe;
    transaction_exe dstrans;
    transaction_exe mstrans;
    mailbox #(transaction_exe) dsmbx;
    mailbox #(transaction_exe) msmbx;
    
    event sconext;
    
    function new (mailbox #(transaction_exe) dsmbx, mailbox #(transaction_exe) msmbx);    
        this.dsmbx   = dsmbx;
        this.msmbx   = msmbx;
    endfunction
    
    task run();       
        forever begin            
            dsmbx.get(dstrans);
            msmbx.get(mstrans);
            
            if (dstrans.op == op_pkg::lea_op) begin
                $display("[SCO-DRV]: [%0g]:                W_control_out: %02h | dr: %03b | sr1: %03b | sr2: %03b | pcout: %04h", $time, dstrans.W_control_out, dstrans.dr, dstrans.sr1, dstrans.sr2, dstrans.pcout);
                $display("[SCO-MON]: [%0g]:                W_control_out: %02h | dr: %03b | sr1: %03b | sr2: %03b | pcout: %04h", $time, mstrans.W_control_out, mstrans.dr, mstrans.sr1, mstrans.sr2, mstrans.pcout);
            
                if (dstrans.W_control_out == mstrans.W_control_out &&
                    dstrans.dr            == mstrans.dr &&
                    dstrans.sr1           == mstrans.sr1 &&
                    dstrans.sr2           == mstrans.sr2 &&
                    dstrans.pcout         == mstrans.pcout)
                    $display("           [%0g]: DATA MATCH", $time);
                else
                    $display("           [%0g]: DATA MISMATCH", $time);
            end else begin
                $display("[SCO-DRV]: [%0g]: aluout: %04h | W_control_out: %02h | dr: %03b | sr1: %03b | sr2: %03b | pcout: %04h", $time, dstrans.aluout, dstrans.W_control_out, dstrans.dr, dstrans.sr1, dstrans.sr2, dstrans.pcout);
                $display("[SCO-MON]: [%0g]: aluout: %04h | W_control_out: %02h | dr: %03b | sr1: %03b | sr2: %03b | pcout: %04h", $time, mstrans.aluout, mstrans.W_control_out, mstrans.dr, mstrans.sr1, mstrans.sr2, mstrans.pcout);
           
                if (dstrans.aluout        == mstrans.aluout &&
                    dstrans.W_control_out == mstrans.W_control_out &&
                    dstrans.dr            == mstrans.dr &&
                    dstrans.sr1           == mstrans.sr1 &&
                    dstrans.sr2           == mstrans.sr2 &&
                    dstrans.pcout         == mstrans.pcout)
                    $display("           [%0g]: DATA MATCH", $time);
                else
                    $display("           [%0g]: DATA MISMATCH", $time);
            end            

            $display("           [%0g]: --------------------------------", $time);

            -> sconext;
        end
    endtask
endclass

/////////////////////////////////

class environment_exe;
    mailbox #(transaction_exe) gdmbx;
    mailbox #(transaction_exe) dsmbx;
    mailbox #(transaction_exe) msmbx;
    
    virtual execute_if vif;
    
    event drvnext;
    event sconext;
    
    generator_exe  gen;
    driver_exe     drv;
    monitor_exe    mon;
    scoreboard_exe sco;
    
    function new (virtual execute_if vif);
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

module execute_tb;
    execute_if vif();
    
    execute dut (
        .clk(vif.clk),
        .rst(vif.rst),
        .enable_execute(vif.enable_execute),
        .E_control(vif.E_control),
        .IR(vif.IR),
        .npc_in(vif.npc_in),
        .W_control_in(vif.W_control_in),
        .aluout(vif.aluout),
        .W_control_out(vif.W_control_out),
        .VSR1(vif.VSR1),
        .VSR2(vif.VSR2),
        .dr(vif.dr),
        .sr1(vif.sr1),
        .sr2(vif.sr2),
        .pcout(vif.pcout)
    );
    
    initial vif.clk <= 0;
    always #5 vif.clk <= ~vif.clk;
    
    environment_exe env;
    
    initial begin
        env = new(vif);
        env.gen.count = 25;
        env.run();
    end
endmodule
