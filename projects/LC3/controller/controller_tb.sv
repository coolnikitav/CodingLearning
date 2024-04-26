`timescale 1ns / 1ps

interface controller_if;
    logic        clk;
    logic        rst;
    logic        enable_updatePC;
    logic        enable_fetch;
    logic [15:0] taddr;
    logic        br_taken;
    logic        enable_decode;
    logic [15:0] Imem_dout;
    logic        enable_execute;
    logic        enable_writeback;
    logic [15:0] memout;
endinterface

/////////////////////////////////

interface instr_memory_if;
    parameter INSTR_MEM_SIZE = 2**16;
    reg [15:0] instr_memory [0:INSTR_MEM_SIZE-1];
endinterface

/////////////////////////////////

typedef enum { fetch, decode, execute, writeback, updatePC } stage_t;

class transaction;   
         stage_t    stage;
         bit        enable_updatePC;
         bit        enable_fetch;
         bit        enable_decode;
         bit        enable_execute;
         bit        enable_writeback;
    rand bit [15:0] taddr;
    rand bit        br_taken;
         bit [15:0] pc;
         bit [15:0] npc;
         bit [15:0] Imem_PC;
         bit [15:0] IR;
         bit [5:0]  E_Control;
         bit [1:0]  W_Control;               
         bit [15:0] aluout;
         bit [1:0]  W_control_out; 
         bit [2:0]  dr;
         bit [2:0]  sr1;
         bit [2:0]  sr2;
         bit [15:0] pcout;
         bit [15:0] VSR1;
         bit [15:0] VSR2;
    
    function transaction copy();
        copy                  = new();
        copy.stage            = this.stage;
        copy.enable_updatePC  = this.enable_updatePC;
        copy.enable_fetch     = this.enable_fetch;
        copy.enable_decode    = this.enable_decode;
        copy.enable_execute   = this.enable_execute;
        copy.enable_writeback = this.enable_writeback;
        copy.taddr            = this.taddr;
        copy.br_taken         = this.br_taken;
        copy.pc               = this.pc;
        copy.npc              = this.npc;
        copy.Imem_PC          = this.Imem_PC;
        copy.IR               = this.IR;
        copy.E_Control        = this.E_Control;
        copy.W_Control        = this.W_Control;
        copy.aluout           = this.aluout;
        copy.W_control_out    = this.W_control_out;
        copy.dr               = this.dr;
        copy.sr1              = this.sr1;
        copy.sr2              = this.sr2;
        copy.pcout            = this.pcout;
        copy.VSR1             = this.VSR1;
        copy.VSR2             = this.VSR2;
    endfunction
    
    constraint taddr_cntrl {
        taddr inside {[16'h3000:16'h4095]};
    }
endclass

/////////////////////////////////

class generator;
    transaction gdtrans;
    mailbox #(transaction) gdmbx;
    
    event drvnext;
    event sconext;
    event done;
    
    int count = 0;
    
    function new (mailbox #(transaction) gdmbx);
        this.gdmbx = gdmbx;
    endfunction
    
    task run();
        for (int i = 0; i < count; i++) begin
            gdtrans = new();
            assert(gdtrans.randomize()) else $error("RANDOMIZATION FAILED");
            if (i < 4) gdtrans.br_taken = 1'b0;  // the first 4 instructions should follow the project example. None of them take the branch
            $display("---------------------------------------------------------------------------------------");
            $display("[GEN]:     [%0g]: taddr: %04h | br_taken: %0b", $time, gdtrans.taddr, gdtrans.br_taken);
            gdmbx.put(gdtrans.copy());
            
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
    
    virtual controller_if vif;
    virtual instr_memory_if vim;
    
    event drvnext;
    
    reg [15:0] reg_file [7:0];
    
    function new (mailbox #(transaction) gdmbx, mailbox #(transaction) dsmbx);
        dstrans    = new();
        this.gdmbx = gdmbx;
        this.dsmbx = dsmbx;
    endfunction
    
    task reset();
        vif.rst              <= 1'b1;
        vif.enable_updatePC  <= 1'b0;
        vif.enable_fetch     <= 1'b0;
        vif.enable_decode    <= 1'b0;
        vif.enable_execute   <= 1'b0;
        vif.enable_writeback <= 1'b0;
        vif.br_taken         <= 1'b0;

        dstrans.pc            = 16'h3000;
        dstrans.npc           = 16'h3001;
        dstrans.Imem_PC       = 16'hxxxx;
        dstrans.IR            = 16'h0000;
        dstrans.aluout        = 16'h0000;
        
        for (int i = 0; i < 8; i++) begin
            reg_file[i] = 16'h0;
        end                        
        repeat(3) @(posedge vif.clk);
        vif.rst              <= 1'b0;
        $display("[DRV]:     [%0g]: RESET DONE", $time);
    endtask
    
    task execute_op();
        vif.rst <= 1'b0;
        /*
         *  Fetch
         */
        vif.enable_updatePC  <= 1'b0;
        vif.enable_fetch     <= 1'b1;        
        vif.enable_decode    <= 1'b0;
        vif.enable_execute   <= 1'b0;
        vif.enable_writeback <= 1'b0;
        @(posedge vif.clk);
        
        $display("[DRV]:     [%0g]: Entered Fetch", $time);  
        dstrans.stage         = fetch;        
        dsmbx.put(dstrans.copy());   
        
        /*
         *  Decode
         */
        vif.enable_updatePC  <= 1'b0;
        vif.enable_fetch     <= 1'b0;
        vif.enable_decode    <= 1'b1;
        vif.enable_execute   <= 1'b0;
        vif.enable_writeback <= 1'b0;
        @(posedge vif.clk);
        
        $display("[DRV]:     [%0g]: Entered Decode", $time);
        dstrans.stage         = decode;
        dstrans.npc           = dstrans.npc;
        dstrans.IR            = vim.instr_memory[dstrans.pc];
        dstrans.E_Control     = compute_dstrans_E_Control(dstrans.IR);
        dstrans.W_Control     = compute_dstrans_W_Control(dstrans.IR);
        dsmbx.put(dstrans.copy());
        
        /*
         *  Execute
         */      
        vif.enable_updatePC  <= 1'b0;
        vif.enable_fetch     <= 1'b0;
        vif.enable_decode    <= 1'b0;
        vif.enable_execute   <= 1'b1;
        vif.enable_writeback <= 1'b0;
        @(posedge vif.clk);
        
        $display("[DRV]:     [%0g]: Entered Execute", $time);
        dstrans.stage         = execute;
        dstrans.aluout        = compute_dstrans_aluout(dstrans.IR);
        dstrans.W_control_out = dstrans.W_Control;
        dstrans.dr            = dstrans.IR[11:9];
        dstrans.sr1           = dstrans.IR[8:6];        
        dstrans.sr2           = dstrans.IR[2:0];
        dstrans.pcout         = compute_dstrans_pcout(dstrans.IR, dstrans.E_Control, dstrans.npc, reg_file[dstrans.sr1]);
        dsmbx.put(dstrans.copy());
        
        reg_file[dstrans.dr] = dstrans.W_Control == 2'h0 ? dstrans.aluout : dstrans.W_Control == 2'h2 ? dstrans.pcout : 16'h0;
        
        /*
         *  Writeback
         */
        vif.enable_updatePC  <= 1'b0;
        vif.enable_fetch     <= 1'b0;
        vif.enable_decode    <= 1'b0;
        vif.enable_execute   <= 1'b0;
        vif.enable_writeback <= 1'b1;
        @(posedge vif.clk);
        
        $display("[DRV]:     [%0g]: Entered Writeback", $time);
        dstrans.stage         = writeback;
        dstrans.VSR1          = reg_file[dstrans.sr1];
        dstrans.VSR2          = reg_file[dstrans.sr2];
        dsmbx.put(dstrans.copy()); 
        
        /*
         *  UpdatePC
         */
        vif.enable_updatePC  <= 1'b1;
        vif.enable_fetch     <= 1'b0;
        vif.taddr            <= gdtrans.taddr;
        vif.br_taken         <= gdtrans.br_taken;
        vif.enable_decode    <= 1'b0;
        vif.enable_execute   <= 1'b0;
        vif.enable_writeback <= 1'b0;
        @(posedge vif.clk);
        
        $display("[DRV]:     [%0g]: Updated PC", $time);
        dstrans.stage         = updatePC;        
        if (gdtrans.br_taken == 1'b1) begin
            dstrans.pc  = gdtrans.taddr;
            dstrans.npc = dstrans.pc+1;
        end else begin
            dstrans.pc            = dstrans.pc+1;
            dstrans.npc           = dstrans.npc+1;
        end
        dsmbx.put(dstrans.copy());  
    endtask
    
    function bit [5:0] compute_dstrans_E_Control (bit [15:0] IR);
        case (IR[15:12])
            4'b0001: begin
                case (IR[5])
                    1'b0: return 6'b00_0001;
                    1'b1: return 6'b00_0000;
                endcase
            end
            4'b0101: begin
                case (IR[5])
                    1'b0: return 6'b01_0001;
                    1'b1: return 6'b01_0000;
                endcase
            end
            4'b1001: return 6'b10_0000;
            4'b1110: return 6'b00_0110;
        endcase
    endfunction
    
    function bit [1:0] compute_dstrans_W_Control (bit [15:0] IR);
        case (IR[15:12])
            4'b0001: return 2'h0;
            4'b0101: return 2'h0;
            4'b1001: return 2'h0;
            4'b1110: return 2'h2;
        endcase
    endfunction
    
    function bit [15:0] compute_dstrans_aluout (bit [15:0] IR);
        case (IR[15:12])
            4'b0001: begin
                case (IR[5])
                    1'b0: return reg_file[IR[8:6]] + reg_file[IR[2:0]];         // VSR1 + VSR2
                    1'b1: return reg_file[IR[8:6]] + { {11{IR[4]}}, IR[4:0] };  // VSR1 + imm5
                endcase
            end
            4'b0101: begin
                case (IR[5])
                    1'b0: return reg_file[IR[8:6]] & reg_file[IR[2:0]];         // VSR1 + VSR2
                    1'b1: return reg_file[IR[8:6]] & { {11{IR[4]}}, IR[4:0] };  // VSR1 + imm5
                endcase
            end
            4'b1001:      return ~reg_file[IR[8:6]];                            // ~VSR1
            4'b1110:      return reg_file[IR[8:6]] + { {11{IR[4]}}, IR[4:0] };  // VSR1 + imm5
        endcase
    endfunction
    
    function bit [15:0] compute_dstrans_pcout (bit [15:0] IR, bit [5:0] E_control, bit [15:0] npc, bit [15:0] VSR1);
        bit [15:0] pcout1, pcout2;
        
        case (E_control[3:2])
            2'h0: pcout1 = { {5{IR[10]}}, IR[10:0] };
            2'h1: pcout1 = {  {7{IR[8]}}, IR[8:0]  };
            2'h2: pcout1 = { {10{IR[5]}}, IR[5:0]  };
            2'h3: pcout1 = 0;
        endcase
        
        pcout2 = E_control[1] == 1'b1 ? npc : VSR1;
        
        return pcout1 + pcout2;
    endfunction
    
    task run();
        forever begin
            gdmbx.get(gdtrans);
            execute_op();
            -> drvnext;
        end
    endtask
endclass

/////////////////////////////////

class monitor;
    transaction mstrans;
    mailbox #(transaction) msmbx;
    
    virtual controller_if vif;
        
    function new (mailbox #(transaction) msmbx);
        this.msmbx = msmbx;
    endfunction
    task run();        
        forever begin
             
            @(posedge vif.clk); #0.001;  // dut signal updates right after a clock edge  
            mstrans         = new(); 
            mstrans.pc            = controller_tb.dut.f.pc;
            mstrans.npc           = controller_tb.dut.f.npc;
            mstrans.Imem_PC       = vif.Imem_dout;
            mstrans.IR            = controller_tb.dut.d.IR;
            mstrans.E_Control     = controller_tb.dut.d.E_Control;
            mstrans.W_Control     = controller_tb.dut.d.W_Control;
            mstrans.aluout        = controller_tb.dut.e.aluout;
            mstrans.W_control_out = controller_tb.dut.e.W_control_out; 
            mstrans.dr            = controller_tb.dut.e.dr;
            mstrans.sr1           = controller_tb.dut.e.sr1;
            mstrans.sr2           = controller_tb.dut.e.sr2;
            mstrans.pcout         = controller_tb.dut.e.pcout;
            mstrans.VSR1          = controller_tb.dut.w.VSR1;
            mstrans.VSR2          = controller_tb.dut.w.VSR2;
            msmbx.put(mstrans.copy());     
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
    
    int data_matches    = 0;
    int data_mismatches = 0;
    
    function new(mailbox #(transaction) dsmbx, mailbox #(transaction) msmbx);        
        this.dsmbx = dsmbx;
        this.msmbx = msmbx;
    endfunction
    
    task check_fetch();
        $display("[SCO-DRV]: [%0g]: pc: %04h | npc: %04h", $time, dstrans.pc, dstrans.npc);
        $display("[SCO-MON]: [%0g]: pc: %04h | npc: %04h", $time, mstrans.pc, mstrans.npc);
    
        if (dstrans.pc      == mstrans.pc &&
            dstrans.npc     == mstrans.npc)
            print_data_match();
        else
            print_data_mismatch();
        print_divider();
    endtask
    
    task check_decode();
        $display("[SCO-DRV]: [%0g]: npc: %04h | IR: %04h | E_control: %06b | W_control: %02b", $time, dstrans.npc, dstrans.IR, dstrans.E_Control, dstrans.W_Control);
        $display("[SCO-MON]: [%0g]: npc: %04h | IR: %04h | E_control: %06b | W_control: %02b", $time, mstrans.npc, mstrans.IR, mstrans.E_Control, mstrans.W_Control);
    
        if (dstrans.npc       == mstrans.npc &&
            dstrans.IR        == mstrans.IR && 
            dstrans.E_Control == mstrans.E_Control &&
            dstrans.W_Control == mstrans.W_Control)
            print_data_match();
        else
            print_data_mismatch();
        print_divider();       
    endtask
    
    task check_execute();
        $display("[SCO-DRV]: [%0g]: aluout: %04h | W_Control_out: %02b | dr: %01h | sr1: %01h | sr2: %01h | pcout: %04h", $time, dstrans.aluout, dstrans.W_control_out, dstrans.dr, dstrans.sr1, dstrans.sr2, dstrans.pcout);
        $display("[SCO-MON]: [%0g]: aluout: %04h | W_Control_out: %02b | dr: %01h | sr1: %01h | sr2: %01h | pcout: %04h", $time, mstrans.aluout, mstrans.W_control_out, mstrans.dr, mstrans.sr1, mstrans.sr2, mstrans.pcout);
        
        if (dstrans.aluout        == mstrans.aluout &&
            dstrans.W_control_out == mstrans.W_control_out && 
            dstrans.dr            == mstrans.dr &&
            dstrans.sr1           == mstrans.sr1 &&
            dstrans.sr2           == mstrans.sr2 &&
            dstrans.pcout         == mstrans.pcout)
            print_data_match();
        else
            print_data_mismatch();
        print_divider();         
    endtask
                
    task check_writeback();
        $display("[SCO-DRV]: [%0g]: VSR1: %04h | VSR2: %04h", $time, dstrans.VSR1, dstrans.VSR2);
        $display("[SCO-MON]: [%0g]: VSR1: %04h | VSR2: %04h", $time, mstrans.VSR1, mstrans.VSR2);
        
        if (dstrans.VSR1 == mstrans.VSR1 &&
            dstrans.VSR2 == mstrans.VSR2)
            print_data_match();
        else
            print_data_mismatch();
        print_divider();                     
    endtask
                            
    task check_updatePC();
        $display("[SCO-DRV]: [%0g]: pc: %04h | npc: %04h", $time, dstrans.pc, dstrans.npc);
        $display("[SCO-MON]: [%0g]: pc: %04h | npc: %04h", $time, mstrans.pc, mstrans.npc);
    
        if (dstrans.pc  == mstrans.pc &&
            dstrans.npc == mstrans.npc)
            print_data_match();
        else
            print_data_mismatch();
        print_divider();                              
    endtask
    
    task print_data_match();
        $display("           [%0g]: DATA MATCH", $time);
        data_matches++;
    endtask
    
    task print_data_mismatch();
        $error("           [%0g]: DATA MISMATCH", $time);
        data_mismatches++;
    endtask
    
    task print_divider();
        $display("           [%0g]: --------------------------------", $time);
    endtask
    
    task run();
        forever begin                       
            dsmbx.get(dstrans);
            msmbx.get(mstrans);
            
            case (dstrans.stage)
                fetch:     check_fetch();
                decode:    check_decode();
                execute:   check_execute();
                writeback: check_writeback();
                updatePC:  check_updatePC();
            endcase

            -> sconext;
        end
    endtask
endclass

/////////////////////////////////

class environment;
    mailbox #(transaction) gdmbx;
    mailbox #(transaction) dsmbx;
    mailbox #(transaction) msmbx;
    
    virtual controller_if vif;
    virtual instr_memory_if vim;
    
    event drvnext;
    event sconext;
    event done;
    
    generator  gen;
    driver     drv;
    monitor    mon;
    scoreboard sco;
    
    function new (virtual controller_if vif, virtual instr_memory_if vim);
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
        
        this.vim = vim;
        drv.vim = vim;
        
        gen.drvnext   = drvnext;
        drv.drvnext   = drvnext;
        gen.sconext   = sconext;
        sco.sconext   = sconext;        
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
        $display("TEST RESULTS: %0d MATCHES, %0d MISMATCHES", sco.data_matches, sco.data_mismatches);
        $finish;
    endtask
    
    task run();
        pre_test();
        test();
        post_test();
    endtask
endclass

/////////////////////////////////

module controller_tb;
    /*
     *  Instruction memory population
     */   
    instr_memory_if vim();
    
    bit [3:0]  isntr_15_12;
    bit [11:0] instr_11_0;
    
    initial begin
        vim.instr_memory[16'h3000] = 16'h5020;
        vim.instr_memory[16'h3001] = 16'h1422;
        vim.instr_memory[16'h3002] = 16'h1820;
        vim.instr_memory[16'h3003] = 16'hEC03;
        for (int i = 16'h3004; i < 16'h4096; i++) begin
            isntr_15_12 = op();
            instr_11_0  = $random & 12'hFFF;
            vim.instr_memory[i] = { isntr_15_12, instr_11_0 };
        end
    end
    
    function bit [3:0] op ();
        case ($random % 4)
            0: return 4'h1;  // ADD
            1: return 4'h5;  // AND
            2: return 4'h9;  // NOT
            3: return 4'hE;  // LEA
        endcase
    endfunction     
    
    /*
     *  Interface instantiation
     */
    controller_if vif();
    
    initial vif.clk <= 0;
    always #5 vif.clk <= ~vif.clk;
    
    assign vif.Imem_dout = vim.instr_memory[dut.f.pc];
    /*
     *  DUT instantiation
     */    
   
    controller dut(
        .clk(vif.clk),
        .rst(vif.rst),
        .enable_updatePC(vif.enable_updatePC),
        .enable_fetch(vif.enable_fetch),
        .taddr(vif.taddr),
        .br_taken(vif.br_taken),
        .enable_decode(vif.enable_decode),
        .Imem_dout(vif.Imem_dout),
        .enable_execute(vif.enable_execute),
        .enable_writeback(vif.enable_writeback),
        .memout(vif.memout)
    ); 
    
    /*
     *  Environment instantiation
     */
     environment env;
     
     initial begin
        env = new(vif, vim);
        env.gen.count = 50;
        env.run();
     end
     
     
endmodule