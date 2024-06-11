`timescale 1ns / 1ps
`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////

typedef enum bit  { 
    instr_op,
    reset_op
} op_t;

///////////////////////////////////////////////

typedef enum bit [3:0] {
        // ALU Operations
        ADD_op = 4'b0001,
        AND_op = 4'b0101,
        NOT_op = 4'b1001,        
        
        //Memory Operations
        LD_op  = 4'b0010,
        LDR_op = 4'b0110,
        LDI_op = 4'b1010,
        LEA_op = 4'b1110,
        ST_op  = 4'b0011,
        STR_op = 4'b0111,
        STI_op = 4'b1011,
        
        // Control Operations
        BR_op  = 4'b0000,
        JMP_op = 4'b1100
    } instr_t;

///////////////////////////////////////////////

interface instr_mem_if;
    parameter INSTR_MEM_SIZE = 2**16;
    reg [15:0] instr_mem [0:INSTR_MEM_SIZE-1];
    
    initial begin
        for (int i = 0; i < INSTR_MEM_SIZE; i++) begin
            instr_mem[i] = {op_t'($urandom_range(0, 11)), $urandom & 12'hFFF};
        end
        instr_mem[16'h3000] = 16'h5020;  // AND // R0 <- R0 & 0 
        instr_mem[16'h3001] = 16'h2C20;  // LD  // R6 <- DMem[3024]
        instr_mem[16'h3002] = 16'h1422;  // ADD // R2 <- R0 + 2
        instr_mem[16'h3003] = 16'h1280;  // ADD // R1 <- R2 + 0)
        instr_mem[16'h3004] = 16'hC180;  // JMP // JMP R6
        instr_mem[16'h3008] = 16'h967F;  // NOT // R3 <- ~R1
        instr_mem[16'h3009] = 16'h3600;  // ST  // R3 -> DMem[300A]
        instr_mem[16'h300A] = 16'h1A83;  // ADD // R5 <- R2 + R3
        instr_mem[16'h300B] = 16'hA802;  // LDI // R4 <- DMem[3010]
        instr_mem[16'h300C] = 16'h5B01;  // AND // R5 <- R4 & R1
        instr_mem[16'h300D] = 16'h0A04;  // BR  // R5 != 0
        instr_mem[16'h3012] = 16'h52A4;  // ADD // R1 <- R2 + 4
        instr_mem[16'h3013] = 16'h6F82;  // LDR // R7 <- DMem[300A]
        instr_mem[16'h3014] = 16'hEBF8;  // LEA // R5 <- 300C
        instr_mem[16'h3015] = 16'hB804;  // STI // R4 -> DMem[301B]
        instr_mem[16'h3016] = 16'h7545;  // STR // R2 -> DMem[3011]
    end
    
endinterface

///////////////////////////////////////////////

interface data_mem_if;
    parameter DATA_MEM_SIZE = 2**16;
    reg [15:0] data_mem [0:DATA_MEM_SIZE-1];
    
    initial begin
        for (int i = 0; i < DATA_MEM_SIZE; i++) begin
            data_mem[i] = {op_t'($urandom_range(0, 11)), $urandom & 12'hFFF};
        end
        data_mem[16'h300A] = 16'h300B;
        data_mem[16'h300E] = 16'h3010;
        data_mem[16'h3010] = 16'h0015;
        data_mem[16'h301A] = 16'h301B;
        data_mem[16'h3024] = 16'h3008;
    end
endinterface

///////////////////////////////////////////////

class transaction extends uvm_sequence_item;
    `uvm_object_utils(transaction)
    
    op_t         op;
    logic        complete_data;
    logic        complete_instr;
    logic [15:0] Instr_dout;
    logic [15:0] Data_dout;
    logic [15:0] PC;
    logic        instrmem_rd;
    logic        Data_addr;
    logic        Data_din;
    logic        Data_rd;        
    
    function new(string name = "transaction");
        super.new(name);
    endfunction
endclass

///////////////////////////////////////////////

class instr extends uvm_sequence#(transaction);
    `uvm_object_utils(instr)
    
    transaction tr;
    
    function new(string name = "instr");
        super.new(name);
    endfunction
    
    virtual task body();
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op = instr_op;
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
        finish_item(tr);
    endtask
endclass

///////////////////////////////////////////////

class driver extends uvm_driver#(transaction);
    `uvm_component_utils(driver)
    
    virtual LC3_if       LC3_vif;
    virtual instr_mem_if instr_mem_vif;
    virtual data_mem_if  data_mem_vif;
    transaction tr;
    
    function new(input string path = "driver", uvm_component parent = null);
        super.new(path, parent);
    endfunction    
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        if(!(uvm_config_db#(virtual LC3_if)::get(this,"","LC3_vif",LC3_vif) &&
             uvm_config_db#(virtual instr_mem_if)::get(this,"","instr_mem_vif",instr_mem_vif) &&
             uvm_config_db#(virtual data_mem_if)::get(this,"","data_mem_vif",data_mem_vif)))
            `uvm_error("MON", "Unable to access interfaces");
    endfunction
    
    task print_inputs();
        `uvm_info("DRV", $sformatf("rst: %01b, complete_data: %01b, complete_instr: %01b, Instr_dout: %04h, Data_dout: %04h",
                                    vif.rst,
                                    vif.complete_data,
                                    vif.complete_instr,
                                    vif.Instr_dout,
                                    vif.Data_dout), UVM_NONE);
    endtask
    
    task instr();
        vif.rst            <= 1'b0;
        vif.complete_data  <= 1'b0;
        vif.complete_instr <= 1'b0; 
        vif.Instr_dout     <= 16'b0;
        vif.Data_dout      <= 16'b0;    
        @(posedge vif.clk);
        vif.Instr_dout     <= vif.instrmem_rd ? 
    endtask
    
    task reset();
        vif.rst            <= 1'b1;
        vif.complete_data  <= 1'b0;
        vif.complete_instr <= 1'b0; 
        vif.Instr_dout     <= 16'b0;
        vif.Data_dout      <= 16'b0;
        repeat(5) @(posedge vif.clk);
        print_inputs();
    endtask
    
    virtual task run_phase(uvm_phase phase);
        forever begin           
            seq_item_port.get_next_item(tr);
            
            seq_item_port.item_done();
        end
    endtask
endclass

///////////////////////////////////////////////

class monitor extends uvm_monitor;
    `uvm_component_utils(monitor)
    
    uvm_analysis_port#(transaction) send;
    
    virtual LC3_if       LC3_vif;
    virtual instr_mem_if instr_mem_vif;
    virtual data_mem_if  data_mem_vif;
    transaction tr;
    
    function new(input string inst = "monitor", uvm_component parent = null);
        super.new(inst, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        tr = transaction::type_id::create("tr");
        send = new("send", this);
        if(!(uvm_config_db#(virtual LC3_if)::get(this,"","LC3_vif",LC3_vif) &&
             uvm_config_db#(virtual instr_mem_if)::get(this,"","instr_mem_vif",instr_mem_vif) &&
             uvm_config_db#(virtual data_mem_if)::get(this,"","data_mem_vif",data_mem_vif)))
            `uvm_error("MON", "Unable to access interfaces");
    endfunction    
    
    virtual task run_phase(uvm_phase phase);
        forever begin
            @(posedge vif.clk); #0.001;

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
    
    virtual function void write(transaction tr);

        $display("---------------------------------------------");
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
    
    environment e;

    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        e      = environment::type_id::create("environment", this);
   
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        phase.drop_objection(this);
    endtask
endclass

///////////////////////////////////////////////

module LC3_tb;
    LC3_if       LC3_vif();
    instr_mem_if instr_mem_vif();
    data_mem_if  data_mem_vif();
    
    LC3 dut(
        .clk(vif.clk),
        .rst(vif.rst),
        .complete_data(vif.complete_data),
        .complete_instr(vif.complete_instr),
        .Instr_dout(vif.Instr_dout),
        .Data_dout(vif.Data_dout),
        .PC(vif.PC),
        .instrmem_rd(vif.instrmem_rd),
        .Data_addr(vif.Data_addr),
        .Data_din(vif.Data_din),
        .Data_rd(vif.Data_rd)
    );
    
    initial begin
        vif.clk <= 0;        
    end
    
    always #5 vif.clk <= ~vif.clk;
    
    initial begin
        uvm_config_db#(virtual LC3_if)::set(null, "*", "LC3_vif", LC3_vif);
        uvm_config_db#(virtual instr_mem_if)::set(null, "*", "instr_mem_vif", instr_mem_vif);
        uvm_config_db#(virtual data_mem_if)::set(null, "*", "data_mem_vif", data_mem_vif);
        run_test("test");
    end   
endmodule
