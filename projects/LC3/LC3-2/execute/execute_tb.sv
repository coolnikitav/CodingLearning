`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////

typedef enum bit [2:0] {  
    no_dependencies_op,
    bypass_alu1_op,
    bypass_alu2_op,
    bypass_mem1_op,
    bypass_mem2_op,
    no_update_op,
    reset_op
} op_t;

///////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
         op_t         op;
         logic        enable_execute;
         logic [5:0]  E_Control_in;
         logic [1:0]  W_Control_in;
         logic        Mem_Control_in;
         logic        bypass_alu_1;
         logic        bypass_alu_2;
         logic        bypass_mem_1;
         logic        bypass_mem_2;
    rand logic [15:0] IR;
    rand logic [15:0] npc_in;
    rand logic [15:0] Mem_Bypass_val;
         logic [15:0] aluout;
         logic [1:0]  W_Control_out;
         logic        Mem_Control_out;
         logic [15:0] M_Data;
    rand logic [15:0] VSR1;
    rand logic [15:0] VSR2;
         logic [2:0]  dr;
         logic [2:0]  sr1;
         logic [2:0]  sr2;
         logic [15:0] pcout;
         logic [2:0]  NZP;
         logic [15:0] IR_Exec;     
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
    
    constraint IR_cntrl {
        IR[15:12] inside {
            4'b0001,  // ADD
            4'b0101,  // AND
            4'b1001,  // NOT
            4'b0000,  // BR
            4'b1100,  // JMP
            4'b0010,  // LD
            4'b0110,  // LDR
            4'b1010,  // LDI
            4'b1110,  // LEA
            4'b0011,  // ST
            4'b0111,  // STR
            4'b1011   // STI  
        };
    };
endclass

///////////////////////////////////////////////

class no_dependencies extends uvm_sequence#(transaction);
    `uvm_object_utils(no_dependencies)
    
    transaction tr;
    
    function new(string name = "no_dependencies");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = no_dependencies_op;
        tr.bypass_alu_1 = 1'b0;
        tr.bypass_alu_2 = 1'b0;
        tr.bypass_mem_1 = 1'b0;
        tr.bypass_mem_2 = 1'b0;
        `uvm_info("SEQ", $sformatf("MODE: NO DEPENDENCIES: IR %016b | npc_in: %04h | VSR1: %04h | VSR2: %04h", 
                                                           tr.IR, 
                                                           tr.npc_in,
                                                           tr.VSR1,
                                                           tr.VSR2), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class bypass_alu1 extends uvm_sequence#(transaction);
    `uvm_object_utils(bypass_alu1)
    
    transaction tr;
    
    function new(string name = "bypass_alu1");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = bypass_alu1_op;
        tr.bypass_alu_1 = 1'b1;
        tr.bypass_alu_2 = 1'b0;
        tr.bypass_mem_1 = 1'b0;
        tr.bypass_mem_2 = 1'b0;
        `uvm_info("SEQ", $sformatf("MODE: BYPASS ALU 1: IR %016b | npc_in: %04h | VSR1: %04h | VSR2: %04h", 
                                                        tr.IR, 
                                                        tr.npc_in,
                                                        tr.VSR1,
                                                        tr.VSR2), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class bypass_alu2 extends uvm_sequence#(transaction);
    `uvm_object_utils(bypass_alu2)
    
    transaction tr;
    
    function new(string name = "bypass_alu2");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = bypass_alu2_op;
        tr.bypass_alu_1 = 1'b0;
        tr.bypass_alu_2 = 1'b1;
        tr.bypass_mem_1 = 1'b0;
        tr.bypass_mem_2 = 1'b0;
        `uvm_info("SEQ", $sformatf("MODE: BYPASS ALU 2: IR %016b | npc_in: %04h | VSR1: %04h | VSR2: %04h", 
                                                        tr.IR, 
                                                        tr.npc_in,
                                                        tr.VSR1,
                                                        tr.VSR2), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class bypass_mem1 extends uvm_sequence#(transaction);
    `uvm_object_utils(bypass_mem1)
    
    transaction tr;
    
    function new(string name = "bypass_mem1");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = bypass_mem1_op;
        tr.bypass_alu_1 = 1'b0;
        tr.bypass_alu_2 = 1'b0;
        tr.bypass_mem_1 = 1'b1;
        tr.bypass_mem_2 = 1'b0;
        `uvm_info("SEQ", $sformatf("MODE: BYPASS MEM 1: IR %016b | npc_in: %04h | VSR1: %04h | VSR2: %04h | Mem_Bypass_val: %04h", 
                                                        tr.IR, 
                                                        tr.npc_in,
                                                        tr.VSR1,
                                                        tr.VSR2,
                                                        tr.Mem_Bypass_val), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class bypass_mem2 extends uvm_sequence#(transaction);
    `uvm_object_utils(bypass_mem2)
    
    transaction tr;
    
    function new(string name = "bypass_mem2");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = bypass_mem2_op;
        tr.bypass_alu_1 = 1'b0;
        tr.bypass_alu_2 = 1'b0;
        tr.bypass_mem_1 = 1'b0;
        tr.bypass_mem_2 = 1'b1;
        `uvm_info("SEQ", $sformatf("MODE: BYPASS MEM 2: IR %016b | npc_in: %0hh | VSR1: %04h | VSR2: %04h | Mem_Bypass_val: %04h", 
                                                        tr.IR, 
                                                        tr.npc_in,
                                                        tr.VSR1,
                                                        tr.VSR2,
                                                        tr.Mem_Bypass_val), UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class no_update extends uvm_sequence#(transaction);
    `uvm_object_utils(no_update)
    
    transaction tr;
    
    function new(string name = "no_update");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = no_update_op;
        tr.bypass_alu_1 = 1'b0;
        tr.bypass_alu_2 = 1'b0;
        tr.bypass_mem_1 = 1'b0;
        tr.bypass_mem_2 = 1'b0;
        `uvm_info("SEQ", "MODE: EXECUTE NOT ENABLED", UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class reset extends uvm_sequence#(transaction);
    `uvm_object_utils(reset)
    
    transaction tr;
    
    function new(string name = "reset");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = reset_op;
        tr.bypass_alu_1 = 1'b0;
        tr.bypass_alu_2 = 1'b0;
        tr.bypass_mem_1 = 1'b0;
        tr.bypass_mem_2 = 1'b0;
        `uvm_info("SEQ", "MODE: RESET", UVM_NONE);
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    `uvm_component_utils(driver)
    
    virtual execute_if vif;
    transaction tr;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction    
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!uvm_config_db#(virtual execute_if)::get(this,"","vif",vif))
            `uvm_error("DRV","Unable to access interface");
    endfunction
    
    function logic [5:0] calc_e_control (input bit [15:0] IR);
        case (IR[15:12])
            4'b0001: begin
                if (IR[5])  
                    return 6'b000000;   //ADD_REG
                else
                    return 6'b000001;   //ADD_IMM
            end
            4'b0101: begin
                if (IR[5])
                    return 6'b010000;   // AND_REG
                else 
                    return 6'b010001;   // AND_IMM
            end
            4'b1001: return 6'b100000;  // NOT
            4'b0000: return 6'b000110;  // BR
            4'b1100: return 6'b001100;  // JMP
            4'b0010: return 6'b000110;  // LD
            4'b0110: return 6'b001000;  // LDR
            4'b1010: return 6'b000110;  // LDI
            4'b1110: return 6'b000110;  // LEA
            4'b0011: return 6'b000110;  // ST
            4'b0111: return 6'b001000;  // STR
            4'b1011: return 6'b000110;  // STI 
        endcase
    endfunction
    
    function logic [1:0] calc_w_control (input bit [15:0] IR);
        case(IR[15:12])
            4'b0001: return 2'h0;  // ADD
            4'b0101: return 2'h0;  // AND
            4'b1001: return 2'h0;  // NOT
            4'b0000: return 2'h0;  // BR
            4'b1100: return 2'h0;  // JMP
            4'b0010: return 2'h1;  // LD
            4'b0110: return 2'h1;  // LDR
            4'b1010: return 2'h1;  // LDI
            4'b1110: return 2'h2;  // LEA
            4'b0011: return 2'h0;  // ST
            4'b0111: return 2'h0;  // STR
            4'b1011: return 2'h0;  // STI     
        endcase
    endfunction
    
    function logic calc_mem_control (input bit [15:0] IR);
        case(IR[15:12])
            4'b0001: return 1'h0;  // ADD
            4'b0101: return 1'h0;  // AND
            4'b1001: return 1'h0;  // NOT
            4'b0000: return 1'h0;  // BR
            4'b1100: return 1'h0;  // JMP
            4'b0010: return 1'h0;  // LD
            4'b0110: return 1'h0;  // LDR
            4'b1010: return 1'h1;  // LDI
            4'b1110: return 1'h0;  // LEA
            4'b0011: return 1'h0;  // ST
            4'b0111: return 1'h0;  // STR
            4'b1011: return 1'h1;  // STI     
        endcase
    endfunction
    
    task no_dependecies();
        vif.rst            <= 1'b0;
        vif.enable_execute <= 1'b1;
        vif.E_Control_in   <= calc_e_control(tr.IR);
        vif.W_Control_in   <= calc_w_control(tr.IR);
        vif.Mem_Control_in <= calc_mem_control(tr.IR);
        vif.bypass_alu_1   <= tr.bypass_alu_1;
        vif.bypass_alu_2   <= tr.bypass_alu_2;
        vif.bypass_mem_1   <= tr.bypass_mem_1;
        vif.bypass_mem_2   <= tr.bypass_mem_2;
        vif.IR             <= tr.IR;
        vif.npc_in         <= tr.npc_in;
        vif.Mem_Bypass_val <= tr.Mem_Bypass_val;
        vif.VSR1           <= tr.VSR1;
        vif.VSR2           <= tr.VSR2;
        @(posedge vif.clk);
        `uvm_info("DRV", $sformatf("MODE: NO DEPENDECIES: IR %016b | npc_in: %04h | VSR1: %04h | VSR2: %04h", 
                                                          tr.IR, 
                                                          tr.npc_in,
                                                          tr.VSR1,
                                                          tr.VSR2), UVM_NONE); #0.002;
    endtask
    
    task bypass_alu1();
        vif.rst            <= 1'b0;
        vif.enable_execute <= 1'b1;
        vif.E_Control_in   <= calc_e_control(tr.IR);
        vif.W_Control_in   <= calc_w_control(tr.IR);
        vif.Mem_Control_in <= calc_mem_control(tr.IR);
        vif.bypass_alu_1   <= tr.bypass_alu_1;
        vif.bypass_alu_2   <= tr.bypass_alu_2;
        vif.bypass_mem_1   <= tr.bypass_mem_1;
        vif.bypass_mem_2   <= tr.bypass_mem_2;
        vif.IR             <= tr.IR;
        vif.npc_in         <= tr.npc_in;
        vif.Mem_Bypass_val <= tr.Mem_Bypass_val;
        vif.VSR1           <= tr.VSR1;
        vif.VSR2           <= tr.VSR2;
        @(posedge vif.clk);
        `uvm_info("DRV", $sformatf("MODE: BYPASS ALU 1: IR %016b | npc_in: %04h | VSR1: %04h | VSR2: %04h", 
                                                        tr.IR, 
                                                        tr.npc_in,
                                                        tr.VSR1,
                                                        tr.VSR2), UVM_NONE); #0.002;
    endtask
    
    task bypass_alu2();
        vif.rst            <= 1'b0;
        vif.enable_execute <= 1'b1;
        vif.E_Control_in   <= calc_e_control(tr.IR);
        vif.W_Control_in   <= calc_w_control(tr.IR);
        vif.Mem_Control_in <= calc_mem_control(tr.IR);
        vif.bypass_alu_1   <= tr.bypass_alu_1;
        vif.bypass_alu_2   <= tr.bypass_alu_2;
        vif.bypass_mem_1   <= tr.bypass_mem_1;
        vif.bypass_mem_2   <= tr.bypass_mem_2;
        vif.IR             <= tr.IR;
        vif.npc_in         <= tr.npc_in;
        vif.Mem_Bypass_val <= tr.Mem_Bypass_val;
        vif.VSR1           <= tr.VSR1;
        vif.VSR2           <= tr.VSR2;
        @(posedge vif.clk);
        `uvm_info("DRV", $sformatf("MODE: BYPASS ALU 2: IR %016b | npc_in: %04h | VSR1: %04h | VSR2: %04h", 
                                                        tr.IR, 
                                                        tr.npc_in,
                                                        tr.VSR1,
                                                        tr.VSR2), UVM_NONE); #0.002;
    endtask
    
    task bypass_mem1();
        vif.rst            <= 1'b0;
        vif.enable_execute <= 1'b1;
        vif.E_Control_in   <= calc_e_control(tr.IR);
        vif.W_Control_in   <= calc_w_control(tr.IR);
        vif.Mem_Control_in <= calc_mem_control(tr.IR);
        vif.bypass_alu_1   <= tr.bypass_alu_1;
        vif.bypass_alu_2   <= tr.bypass_alu_2;
        vif.bypass_mem_1   <= tr.bypass_mem_1;
        vif.bypass_mem_2   <= tr.bypass_mem_2;
        vif.IR             <= tr.IR;
        vif.npc_in         <= tr.npc_in;
        vif.Mem_Bypass_val <= tr.Mem_Bypass_val;
        vif.VSR1           <= tr.VSR1;
        vif.VSR2           <= tr.VSR2;
        @(posedge vif.clk);
        `uvm_info("DRV", $sformatf("MODE: BYPASS MEM 1: IR %016b | npc_in: %04h | VSR1: %04h | VSR2: %04h | Mem_Bypass_val: %04h", 
                                                        tr.IR, 
                                                        tr.npc_in,
                                                        tr.VSR1,
                                                        tr.VSR2,
                                                        tr.Mem_Bypass_val), UVM_NONE); #0.002;
    endtask
    
    task bypass_mem2();
        vif.rst            <= 1'b0;
        vif.enable_execute <= 1'b1;
        vif.E_Control_in   <= calc_e_control(tr.IR);
        vif.W_Control_in   <= calc_w_control(tr.IR);
        vif.Mem_Control_in <= calc_mem_control(tr.IR);
        vif.bypass_alu_1   <= tr.bypass_alu_1;
        vif.bypass_alu_2   <= tr.bypass_alu_2;
        vif.bypass_mem_1   <= tr.bypass_mem_1;
        vif.bypass_mem_2   <= tr.bypass_mem_2;
        vif.IR             <= tr.IR;
        vif.npc_in         <= tr.npc_in;
        vif.Mem_Bypass_val <= tr.Mem_Bypass_val;
        vif.VSR1           <= tr.VSR1;
        vif.VSR2           <= tr.VSR2;
        @(posedge vif.clk);
        `uvm_info("DRV", $sformatf("MODE: BYPASS MEM 2: IR %016b | npc_in: %04h | VSR1: %04h | VSR2: %04h | Mem_Bypass_val: %04h", 
                                                        tr.IR, 
                                                        tr.npc_in,
                                                        tr.VSR1,
                                                        tr.VSR2,
                                                        tr.Mem_Bypass_val), UVM_NONE); #0.002;
    endtask
    
    task no_update();
        vif.rst            <= 1'b0;
        vif.enable_execute <= 1'b0;
        vif.E_Control_in   <= calc_e_control(tr.IR);
        vif.W_Control_in   <= calc_w_control(tr.IR);
        vif.Mem_Control_in <= calc_mem_control(tr.IR);
        vif.bypass_alu_1   <= tr.bypass_alu_1;
        vif.bypass_alu_2   <= tr.bypass_alu_2;
        vif.bypass_mem_1   <= tr.bypass_mem_1;
        vif.bypass_mem_2   <= tr.bypass_mem_2;
        vif.IR             <= tr.IR;
        vif.npc_in         <= tr.npc_in;
        vif.Mem_Bypass_val <= tr.Mem_Bypass_val;
        vif.VSR1           <= tr.VSR1;
        vif.VSR2           <= tr.VSR2;
        @(posedge vif.clk);
        `uvm_info("DRV", "MODE: EXECUTE NOT ENABLED", UVM_NONE); #0.002;
    endtask
    
    task reset();
        vif.rst            <= 1'b1;
        vif.enable_execute <= 1'b0;
        vif.E_Control_in   <= calc_e_control(tr.IR);
        vif.W_Control_in   <= calc_w_control(tr.IR);
        vif.Mem_Control_in <= calc_mem_control(tr.IR);
        vif.bypass_alu_1   <= tr.bypass_alu_1;
        vif.bypass_alu_2   <= tr.bypass_alu_2;
        vif.bypass_mem_1   <= tr.bypass_mem_1;
        vif.bypass_mem_2   <= tr.bypass_mem_2;
        vif.IR             <= tr.IR;
        vif.npc_in         <= tr.npc_in;
        vif.Mem_Bypass_val <= tr.Mem_Bypass_val;
        vif.VSR1           <= tr.VSR1;
        vif.VSR2           <= tr.VSR2;
        @(posedge vif.clk);
        `uvm_info("DRV", "MODE: RESET", UVM_NONE); #0.002;
    endtask
    
    virtual task run_phase(uvm_phase phase);
        forever begin           
            seq_item_port.get_next_item(tr);
            case(tr.op)
                no_dependencies_op: no_dependecies();
                bypass_alu1_op:    bypass_alu1();
                bypass_alu2_op:    bypass_alu2();                
                bypass_mem1_op:    bypass_mem1();
                bypass_mem2_op:    bypass_mem2();
                no_update_op:      no_update();
                reset_op:          reset();
            endcase
            seq_item_port.item_done();
        end
    endtask
endclass

///////////////////////////////////////////////

class monitor extends uvm_monitor;
    `uvm_component_utils(monitor)
    
    uvm_analysis_port#(transaction) send;
    transaction tr;
    virtual execute_if vif;
    
    function new(input string inst = "monitor", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!uvm_config_db#(virtual execute_if)::get(this,"","vif",vif))
            `uvm_error("MON", "Unable to access interface");
    endfunction    
    
    task print_outputs(string instr);
        `uvm_info("MON", $sformatf("MODE: %0s: aluout: %04h | W_Control_out: %0h | Mem_Control_out: %0b | M_Data: %04h | dr: %01h | sr1: %01h | sr2: %01h | pcout: %04h | NZP: %03b | IR_Exec: %016b", 
                                         instr,
                                         tr.aluout,
                                         tr.W_Control_out,
                                         tr.Mem_Control_out,
                                         tr.M_Data,
                                         tr.dr,
                                         tr.sr1,
                                         tr.sr2,
                                         tr.pcout,
                                         tr.NZP,
                                         tr.IR_Exec), UVM_NONE);
    endtask
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk); #0.001;
            tr.E_Control_in    = vif.E_Control_in;
            tr.W_Control_in    = vif.W_Control_in;
            tr.Mem_Control_in  = vif.Mem_Control_in;
            tr.VSR1            = vif.VSR1;
            tr.VSR2            = vif.VSR2;
            tr.Mem_Bypass_val  = vif.Mem_Bypass_val;
            tr.IR              = vif.IR;
            tr.npc_in          = vif.npc_in;
            tr.aluout          = vif.aluout;
            tr.W_Control_out   = vif.W_Control_out;
            tr.Mem_Control_out = vif.Mem_Control_out;
            tr.M_Data          = vif.M_Data;
            tr.dr              = vif.dr;
            tr.sr1             = vif.sr1;
            tr.sr2             = vif.sr2;
            tr.pcout           = vif.pcout;
            tr.NZP             = vif.NZP;
            tr.IR_Exec         = vif.IR_Exec;
            if (vif.rst) begin
                tr.op = reset_op;
                print_outputs("RESET");
            end else if (vif.bypass_alu_1) begin
                tr.op = bypass_alu1_op;
                print_outputs("BYPASS ALU1");
            end else if (vif.bypass_alu_2) begin
                tr.op = bypass_alu2_op;
                print_outputs("BYPASS ALU2");
            end else if (vif.bypass_mem_1) begin
                tr.op = bypass_mem1_op;
                print_outputs("BYPASS MEM1");
            end else if (vif.bypass_mem_2) begin
                tr.op = bypass_mem2_op;
                print_outputs("BYPASS MEM2");
            end else if (vif.enable_execute) begin
                tr.op = no_dependencies_op;
                print_outputs("NO DEPENDECIES");
            end else begin
                tr.op = no_update_op;
                print_outputs("NO UPDATE");
            end
            send.write(tr);
        end
    endtask
endclass

///////////////////////////////////////////////

class scoreboard extends uvm_scoreboard;
    `uvm_component_utils(scoreboard)
    
    uvm_analysis_imp#(transaction, scoreboard) recv;
    
    function new(input string inst = "scoreboard", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        recv = new("recv", this);
    endfunction        
    
    reg [15:0] prev_aluout;
    
    function logic [15:0] golden_aluout (input op_t       op,
                                         input bit [5:0]  E_Control, 
                                         input bit [15:0] VSR1, 
                                         input bit [15:0] VSR2, 
                                         input bit [15:0] imm5,
                                         input bit [15:0] aluout, 
                                         input bit [15:0] Mem_Bypass_val);
        case (op)
            no_dependencies_op: begin
                case (E_Control[5:4])
                    2'h0: if (E_Control[0]) begin
                        return VSR1 + VSR2;
                    end else begin
                        return VSR1 + imm5;
                    end
                    2'h1: if (E_Control[0]) begin
                        return VSR1 & VSR2;
                    end else begin
                        return VSR1 & imm5;
                    end
                    2'h2: return ~VSR1;
                endcase
            end
            bypass_alu1_op: begin
                case (E_Control[5:4])
                    2'h0: if (E_Control[0]) begin
                        return aluout + VSR2;
                    end else begin
                        return aluout + imm5;
                    end
                    2'h1: if (E_Control[0]) begin
                        return aluout & VSR2;
                    end else begin
                        return aluout & imm5;
                    end
                    2'h2: return ~aluout;
                endcase
            end
            bypass_alu2_op: begin
                case (E_Control[5:4])
                    2'h0: return VSR1 + aluout;
                    2'h1: return VSR1 & aluout;
                    2'h2: return ~VSR1;
                endcase
            end
            bypass_mem1_op: begin
                case (E_Control[5:4])
                    2'h0: if (E_Control[0]) begin
                        return Mem_Bypass_val + VSR2;
                    end else begin
                        return Mem_Bypass_val + imm5;
                    end
                    2'h1: if (E_Control[0]) begin
                        return Mem_Bypass_val & VSR2;
                    end else begin
                        return Mem_Bypass_val & imm5;
                    end
                    2'h2: return ~Mem_Bypass_val;
                endcase
            end
            bypass_mem2_op: begin
                case (E_Control[5:4])
                    2'h0: return VSR1 + Mem_Bypass_val;
                    2'h1: return VSR1 & Mem_Bypass_val;
                    2'h2: return ~VSR1;
                endcase
            end
        endcase
    endfunction
    
    function logic [15:0] golden_pcout (input bit [5:0]  E_Control, 
                                        input bit [15:0] IR,
                                        input bit [15:0] VSR1,
                                        input bit [15:0] npc);
        bit [15:0] pc1, pc2;
        
        case (E_Control[3:2])
            2'h0: pc1 = {  {5{IR[10]}}, IR[10:0] };
            2'h1: pc1 = {  {7{IR[8]}},  IR[8:0]  };
            2'h2: pc1 = { {10{IR[5]}},  IR[5:0]  };
            2'h3: pc1 = 0;
        endcase  
        
        case (E_Control[1])
            1'h0: pc2 = VSR1;
            1'h1: pc2 = npc;
        endcase            
        return pc1 + pc2;                      
    endfunction                                        
    
    virtual function void write(transaction tr);
        case(tr.op)
            no_dependencies_op: begin
                if (tr.aluout          == golden_aluout(tr.op, tr.E_Control_in, tr.VSR1, tr.VSR2, {{11{tr.IR[4]}}, tr.IR[4:0]}, prev_aluout, tr.Mem_Bypass_val) &&
                    tr.W_Control_out   == tr.W_Control_in &&
                    tr.Mem_Control_out == tr.Mem_Control_in &&
                    tr.M_Data          == ((tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011) ? tr.VSR1 : 16'h0) &&
                    tr.dr              == tr.IR[11:9] &&
                    tr.sr1             == tr.IR[8:6] &&
                    tr.sr2             == tr.IR[2:0] &&
                    tr.pcout           == golden_pcout(tr.E_Control_in, tr.IR, tr.VSR1, tr.npc_in) &&
                    tr.NZP             == (tr.IR[15:12] == 4'b0000 ? tr.IR[11:9] : 3'h0) &&
                    tr.IR_Exec         == tr.IR) begin
                    `uvm_info("SCO", "DATA MATCH", UVM_NONE);    
                end else begin
                    `uvm_error("SCO", "DATA MISMATCH");   
                end
            end
            bypass_alu1_op: begin
                if (tr.aluout          == golden_aluout(tr.op, tr.E_Control_in, tr.VSR1, tr.VSR2, {{11{tr.IR[4]}}, tr.IR[4:0]}, prev_aluout, tr.Mem_Bypass_val) &&
                    tr.W_Control_out   == tr.W_Control_in &&
                    tr.Mem_Control_out == tr.Mem_Control_in &&
                    tr.M_Data          == ((tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011) ? prev_aluout : 16'h0) &&
                    tr.dr              == tr.IR[11:9] &&
                    tr.sr1             == tr.IR[8:6] &&
                    tr.sr2             == tr.IR[2:0] &&
                    tr.pcout           == golden_pcout(tr.E_Control_in, tr.IR, tr.VSR1, tr.npc_in) &&
                    tr.NZP             == (tr.IR[15:12] == 4'b0000 ? tr.IR[11:9] : 3'h0) &&
                    tr.IR_Exec         == tr.IR) begin
                    `uvm_info("SCO", "DATA MATCH", UVM_NONE);    
                end else begin
                    `uvm_error("SCO", "DATA MISMATCH");   
                end
            end
            bypass_alu2_op: begin
                if (tr.aluout          == golden_aluout(tr.op, tr.E_Control_in, tr.VSR1, tr.VSR2, {{11{tr.IR[4]}}, tr.IR[4:0]}, prev_aluout, tr.Mem_Bypass_val) &&
                    tr.W_Control_out   == tr.W_Control_in &&
                    tr.Mem_Control_out == tr.Mem_Control_in &&
                    tr.M_Data          == ((tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011) ? tr.VSR1 : 16'h0) &&
                    tr.dr              == tr.IR[11:9] &&
                    tr.sr1             == tr.IR[8:6] &&
                    tr.sr2             == tr.IR[2:0] &&
                    tr.pcout           == golden_pcout(tr.E_Control_in, tr.IR, tr.VSR1, tr.npc_in) &&
                    tr.NZP             == (tr.IR[15:12] == 4'b0000 ? tr.IR[11:9] : 3'h0) &&
                    tr.IR_Exec         == tr.IR) begin
                    `uvm_info("SCO", "DATA MATCH", UVM_NONE);    
                end else begin
                    `uvm_error("SCO", "DATA MISMATCH");   
                end
            end                
            bypass_mem1_op: begin
                if (tr.aluout          == golden_aluout(tr.op, tr.E_Control_in, tr.VSR1, tr.VSR2, {{11{tr.IR[4]}}, tr.IR[4:0]}, prev_aluout, tr.Mem_Bypass_val) &&
                    tr.W_Control_out   == tr.W_Control_in &&
                    tr.Mem_Control_out == tr.Mem_Control_in &&
                    tr.M_Data          == ((tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011) ? tr.Mem_Bypass_val : 16'h0) &&
                    tr.dr              == tr.IR[11:9] &&
                    tr.sr1             == tr.IR[8:6] &&
                    tr.sr2             == tr.IR[2:0] &&
                    tr.pcout           == golden_pcout(tr.E_Control_in, tr.IR, tr.VSR1, tr.npc_in) &&
                    tr.NZP             == (tr.IR[15:12] == 4'b0000 ? tr.IR[11:9] : 3'h0) &&
                    tr.IR_Exec         == tr.IR) begin
                    `uvm_info("SCO", "DATA MATCH", UVM_NONE);                                   
                end else begin
                    `uvm_error("SCO", "DATA MISMATCH");
                end
            end
            bypass_mem2_op: begin
                if (tr.aluout          == golden_aluout(tr.op, tr.E_Control_in, tr.VSR1, tr.VSR2, {{11{tr.IR[4]}}, tr.IR[4:0]}, prev_aluout, tr.Mem_Bypass_val) &&
                    tr.W_Control_out   == tr.W_Control_in &&
                    tr.Mem_Control_out == tr.Mem_Control_in &&
                    tr.M_Data          == ((tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011 || tr.IR[15:12] == 4'b0011) ? tr.VSR1 : 16'h0) &&
                    tr.dr              == tr.IR[11:9] &&
                    tr.sr1             == tr.IR[8:6] &&
                    tr.sr2             == tr.IR[2:0] &&
                    tr.pcout           == golden_pcout(tr.E_Control_in, tr.IR, tr.VSR1, tr.npc_in) &&
                    tr.NZP             == (tr.IR[15:12] == 4'b0000 ? tr.IR[11:9] : 3'h0) &&
                    tr.IR_Exec         == tr.IR) begin
                    `uvm_info("SCO", "DATA MATCH", UVM_NONE);    
                end else begin
                    `uvm_error("SCO", "DATA MISMATCH");   
                end
            end
            no_update_op: begin
                `uvm_info("SCO", "NO UPDATE", UVM_NONE);
            end
            reset_op: begin
                if (tr.aluout          == 16'h0 &&
                    tr.W_Control_out   == 2'h0 &&
                    tr.Mem_Control_out == 1'h0 &&
                    tr.M_Data          == 16'h0 &&
                    tr.dr              == 3'h0 &&                    
                    tr.pcout           == 16'h0 &&
                    tr.NZP             == 3'h0 &&
                    tr.IR_Exec         == 16'h0) begin
                    `uvm_info("SCO", "DATA MATCH", UVM_NONE);    
                end else begin
                    `uvm_error("SCO", "DATA MISMATCH");   
                end
            end
        endcase
        $display("---------------------------------------------");
        prev_aluout = tr.aluout;
    endfunction    
endclass

///////////////////////////////////////////////

class agent extends uvm_agent;
    `uvm_component_utils(agent)
    
    function new(input string inst = "agent", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    driver d;
    uvm_sequencer#(transaction) seqr;
    monitor m;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m = monitor::type_id::create("m", this);
        d = driver::type_id::create("d", this);
        seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        d.seq_item_port.connect(seqr.seq_item_export);
    endfunction
endclass

///////////////////////////////////////////////

class environment extends uvm_env;
    `uvm_component_utils(environment)
    
    function new(input string inst = "environment", uvm_component c);
        super.new(inst, c);
    endfunction
    
    agent a;
    scoreboard s;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        a = agent::type_id::create("a", this);
        s = scoreboard::type_id::create("s", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        a.m.send.connect(s.recv);
    endfunction
endclass

///////////////////////////////////////////////

class test extends uvm_test;
    `uvm_component_utils(test)
    
    function new(input string inst = "test", uvm_component c);
        super.new(inst, c);
    endfunction
    
    environment     e;
    no_dependencies n_d;
    bypass_alu1     b_a1;
    bypass_alu2     b_a2;
    bypass_mem1     b_m1;
    bypass_mem2     b_m2;
    no_update       n_u;
    reset           r;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e    = environment::type_id::create("environment", this);
        n_d  =  no_dependencies::type_id::create("n_d");
        b_a1 = bypass_alu1::type_id::create("b_a1");
        b_a2 = bypass_alu2::type_id::create("b_a2");
        b_m1 = bypass_mem1::type_id::create("b_m1");
        b_m2 = bypass_mem2::type_id::create("b_m2");
        n_u  = no_update::type_id::create("n_u");
        r    = reset::type_id::create("r");
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        r.start(e.a.seqr);  // reset dut to start
        for (int i = 0; i < 100; i++) begin
            case($urandom_range(6))
                4'h0: n_d.start(e.a.seqr);
                4'h1: b_a1.start(e.a.seqr);
                4'h2: b_a2.start(e.a.seqr);
                4'h3: b_m1.start(e.a.seqr);
                4'h4: b_m2.start(e.a.seqr);
                4'h5: n_u.start(e.a.seqr);
                4'h6: r.start(e.a.seqr);
            endcase
        end        
        phase.drop_objection(this);
    endtask
endclass

///////////////////////////////////////////////

module execute_tb;
    execute_if vif();
    
    execute dut(
        .clk(vif.clk),
        .rst(vif.rst),
        .enable_execute(vif.enable_execute),
        .E_Control_in(vif.E_Control_in),
        .W_Control_in(vif.W_Control_in),
        .Mem_Control_in(vif.Mem_Control_in),
        .bypass_alu_1(vif.bypass_alu_1),
        .bypass_alu_2(vif.bypass_alu_2),
        .bypass_mem_1(vif.bypass_mem_1),
        .bypass_mem_2(vif.bypass_mem_2),
        .IR(vif.IR),
        .npc_in(vif.npc_in),
        .Mem_Bypass_val(vif.Mem_Bypass_val),
        .aluout(vif.aluout),
        .W_Control_out(vif.W_Control_out),
        .Mem_Control_out(vif.Mem_Control_out),
        .M_Data(vif.M_Data),
        .VSR1(vif.VSR1),
        .VSR2(vif.VSR2),
        .dr(vif.dr),
        .sr1(vif.sr1),
        .sr2(vif.sr2),
        .pcout(vif.pcout),
        .NZP(vif.NZP),
        .IR_Exec(vif.IR_Exec)
    );
    
    initial begin
        vif.clk <= 0;        
    end
    
    always #5 vif.clk <= ~vif.clk;
    
    initial begin
        uvm_config_db#(virtual execute_if)::set(null, "*", "vif", vif);
        run_test("test");
    end   
endmodule
