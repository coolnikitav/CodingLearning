# Verification of UART

## Design Code
```
module clk_gen(
    input clk, rst,
    input [16:0] baud,
    output reg tx_clk, rx_clk
    );
 
    int rx_max =0, tx_max = 0;
    int rx_count = 0 , tx_count = 0;
     
    always@(posedge clk) begin
		if(rst) begin
			rx_max <= 0;
			tx_max <= 0;	
		end else begin 		
			case(baud)
				4800: begin
                    rx_max <= 11'd651;
					tx_max <= 14'd10416;	
			    end
				9600: begin
				    rx_max <= 11'd325;
					tx_max <= 14'd5208;
				end
				14400: begin 
				    rx_max <= 11'd217;
					tx_max <= 14'd3472;
				end
				19200: begin 
				    rx_max <= 11'd163;
					tx_max <= 14'd2604;
				end
				38400: begin
				    rx_max <= 11'd81;
				    tx_max <= 14'd1302;
				end
				57600: begin 
				    rx_max <= 11'd54;
					tx_max <= 14'd868;	
				end 						
				115200: begin 
				    rx_max <= 11'd27;
					tx_max <= 14'd434;	
				end
				128000: begin 
				    rx_max <=11'd24;
					tx_max <=14'd392;	
				end
			    default: begin 
				    rx_max <=11'd325;
					tx_max <=14'd5208;	
				end
			endcase
		end
	end
 
    always@(posedge clk) begin
        if(rst) begin
            rx_max   <= 0;
            rx_count <= 0;
            rx_clk   <= 0;
        end
        else  begin
            if(rx_count <= rx_max) begin
                 rx_count <= rx_count + 1;
            end else begin
                rx_clk   <= ~rx_clk;
                rx_count <= 0;
            end
        end
    end
 
    always@(posedge clk) begin
        if(rst) begin
            tx_max   <= 0;
            tx_count <= 0;
            tx_clk <= 0;
        end else begin
            if(tx_count <= tx_max) begin
                tx_count <= tx_count + 1;
            end else begin
                tx_clk   <= ~tx_clk;
                tx_count <= 0;
            end
        end
    end
endmodule

//////////////////////////////////////////////////

module uart_tx(
    input tx_clk,tx_start,
    input rst, 
    input [7:0] tx_data,
    input [3:0] length,
    input parity_type,parity_en,
    input stop2,
    output reg tx, tx_done, tx_err
    );
    logic [7:0] tx_reg;
    logic start_b = 0;
    logic stop_b  = 1;
    logic parity_bit = 0;
    integer count = 0;
    
    typedef enum bit [2:0]  {idle = 0, start_bit = 1, send_data = 2, send_parity = 3, send_first_stop = 4, send_sec_stop = 5, done = 6} state_type;
    state_type state = idle, next_state = idle;
    
    ////////////////////parity generator
    always@(posedge tx_clk) begin
       if(parity_type == 1'b1) begin  // odd
        case(length)
            4'd5:    parity_bit = ^(tx_data[4:0]);
            4'd6:    parity_bit = ^(tx_data[5:0]); 
            4'd7:    parity_bit = ^(tx_data[6:0]);
            4'd8:    parity_bit = ^(tx_data[7:0]);
            default: parity_bit = 1'b0; 
        endcase
       end else begin
        case(length)
            4'd5:    parity_bit = ~^(tx_data[4:0]);
            4'd6:    parity_bit = ~^(tx_data[5:0]); 
            4'd7:    parity_bit = ~^(tx_data[6:0]);
            4'd8:    parity_bit = ~^(tx_data[7:0]);
            default: parity_bit = 1'b0; 
        endcase
       end 
    end
    
    ///////////////////// reset detector
    always@(posedge tx_clk)  begin
      if(rst)
        state <= idle;
      else
        state <= next_state;
    end
    
    ///////////////////next state decoder + output decoder
    always@(*) begin
        case(state)
            idle: begin
                tx_done        = 1'b0; 
                tx             = 1'b1;
                tx_reg         = {(8){1'b0}}; 
                tx_err         = 0;
                if(tx_start)
                    next_state = start_bit;
                else
                    next_state = idle;
            end
            start_bit: begin
                tx_reg         = tx_data;
                tx             = start_b;
                next_state     = send_data;
            end  
            send_data: begin
                if(count < (length - 1)) begin
                    next_state = send_data;
                    tx         = tx_reg[count];
                end else if (parity_en) begin
                    tx         = tx_reg[count];
                    next_state = send_parity;
                end else begin
                    tx         = tx_reg[count];
                    next_state = send_first_stop;
                end
            end  
            send_parity: begin
                tx             = parity_bit;
                next_state     = send_first_stop;
            end      
            send_first_stop: begin
                tx             = stop_b;
                if(stop2)
                    next_state = send_sec_stop;       
                else
                    next_state = done;
            end
            send_sec_stop: begin
                tx             = stop_b;
                next_state     = done;
            end
            done: begin
                tx_done        = 1'b1;
                next_state     = idle;
            end
            default : next_state = idle;
        endcase
    end 
 
    always@(posedge tx_clk)  begin
        case(state)
            idle : begin
                count <= 0;
            end
            start_bit : begin
                count  <= 0;
            end 
            send_data: begin
                count <= count + 1;
            end
            send_parity: begin
                count <= 0;
            end 
            send_first_stop : begin
                count <= 0;
            end
            send_sec_stop : begin
                count <= 0;
            end
            done : begin
                count <= 0;
            end
            default : count <= 0;
        endcase
    end
endmodule
 
//////////////////////////////////////////////////
 
module uart_rx(
    input rx_clk,rx_start,
    input rst, rx,
    input [3:0] length,
    input parity_type,parity_en,
    input stop2,
    output reg [7:0] rx_out,
    output logic rx_done, rx_error
    );
    logic parity = 0;   
    logic [7:0] datard = 0;
    int count = 0;
    int bit_count = 0;
 
    typedef enum bit [2:0] {idle = 0, start_bit = 1, recv_data = 2, check_parity = 3, check_first_stop = 4, check_sec_stop= 5, done = 6} state_type;
    state_type state = idle, next_state = idle;
    
    ///////////////////// reset detector
    always@(posedge rx_clk) begin
        if(rst)
            state <= idle;
        else
            state <= next_state;
    end
    
    /////////////////////next_State decoder + output
    ///////////////////// reset detector
    always@(*) begin
        case(state)
            idle: begin
                rx_done  = 0;
                rx_error = 0;
                if(rx_start && !rx)
                    next_state = start_bit;
                else
                    next_state = idle;
            end
            start_bit:  begin
                if(count == 7 && rx)
                    next_state = idle;
                else if (count == 15)
                    next_state = recv_data;
                else
                    next_state = start_bit;
            end
            recv_data: begin
                if(count == 7) begin
                    datard[7:0]   =  {rx,datard[7:1]};   
                end else if(count == 15 && bit_count == (length - 1)) begin
                    case(length)
                         5: rx_out = datard[7:3];
                         6: rx_out = datard[7:2];
                         7: rx_out = datard[7:1];
                         8: rx_out = datard[7:0];
                         default : rx_out = 8'h00;
                    endcase
                    if(parity_type)
                        parity = ^datard;
                    else
                        parity  = ~^datard;
                        if(parity_en)
                            next_state = check_parity;
                        else   
                            next_state = check_first_stop;
                end else
                    next_state = recv_data;   
            end  
            check_parity: begin
              if(count == 7) 
                  begin
                    if(rx == parity)
                       rx_error = 1'b0;
                    else
                       rx_error = 1'b1;
                   end  
             else if (count == 15) 
                    begin  
                    next_state = check_first_stop;
                    end
             else
                    begin
                    next_state = check_parity;
                    end
                        
          end       
            check_first_stop : 
            begin
               if(count == 7)
                   begin
                      if(rx != 1'b1)
                          rx_error = 1'b1;
                      else
                          rx_error = 1'b0;
                   end
                else if (count == 15)
                   begin
                     if(stop2)
                        next_state = check_sec_stop;
                     else
                        next_state = done; 
                   end
            end
            check_sec_stop: begin
              if(count == 7)
                   begin
                      if(rx != 1'b1)
                          rx_error = 1'b1;
                      else
                          rx_error = 1'b0;
                   end
                else if (count == 15)
                   begin
                        next_state = done; 
                   end
            
             end
        done :  begin
           rx_done = 1'b1;
           next_state = idle;
           rx_error = 1'b0;
        end    
  endcase
    end
    
      ///////////////////// reset detector
    always@(posedge rx_clk)
    begin
      case(state)
         idle: 
          begin
             count     <= 0;
             bit_count <= 0;
         end
         start_bit: 
         begin
            if(count < 15)
              count <= count + 1;
            else
              count <= 0;
         end
            recv_data: begin
            if(count < 15)
              count <= count + 1;
            else begin
              count <= 0;
              bit_count <= bit_count + 1;
              end
   
             end  
          check_parity: begin
              if(count < 15)
              count <= count + 1;
            else
              count <= 0;               
          end       
            check_first_stop : 
            begin
             if(count < 15)
              count <= count + 1;
            else
              count <= 0;
            end
            check_sec_stop: begin
             if(count < 15)
              count <= count + 1;
            else
              count <= 0;
             end
        done :  begin
           count <= 0;
           bit_count <= 0;
        end    
  endcase
    end
 endmodule
 
 ///////////////////////////////////////////////////////////////////
 
 module uart_top (
     input clk, rst,
     input tx_start, rx_start,
     input [7:0] tx_data,
     input [16:0] baud,
     input [3:0] length,
     input parity_type, parity_en,
     input stop2,
     output tx_done,rx_done, tx_err,rx_err,
     output [7:0] rx_out
    );
    wire tx_clk, rx_clk;
    wire tx_rx;
     
    clk_gen clk_dut (clk, rst, baud,tx_clk, rx_clk); 
    uart_tx tx_dut (tx_clk,tx_start, rst, tx_data, length, parity_type, parity_en, stop2, tx_rx, tx_done, tx_err);
    uart_rx rx_dut (rx_clk, rx_start, rst, tx_rx, length,parity_type, parity_en, stop2,rx_out,rx_done, rx_err);
endmodule
 
 /////////////////////////////////////////////////////////////////////
 
interface uart_if;
 logic clk, rst;
 logic tx_start, rx_start;
 logic [7:0] tx_data;
 logic [16:0] baud;
 logic [3:0] length;
 logic parity_type, parity_en;
 logic stop2;
 logic tx_done,rx_done, tx_err,rx_err;
 logic [7:0] rx_out;   
endinterface
```
## Verification
```
`include "uvm_macros.svh"
 import uvm_pkg::*;
 
/////////////build the seq for random length with and without priority
 
////////////////////////////////////////////////////////////////////////////////////
class uart_config extends uvm_object; /////configuration of env
  `uvm_object_utils(uart_config)
  
  function new(string name = "uart_config");
    super.new(name);
  endfunction
  
  uvm_active_passive_enum is_active = UVM_ACTIVE;
  
endclass
 
//////////////////////////////////////////////////////////
 
typedef enum bit [3:0]   {rand_baud_1_stop = 0, rand_length_1_stop = 1, length5wp = 2, length6wp = 3, length7wp = 4, length8wp = 5, length5wop = 6, length6wop = 7, length7wop = 8, length8wop = 9,rand_baud_2_stop = 11, rand_length_2_stop = 12} oper_mode;
 
 
class transaction extends uvm_sequence_item;
  `uvm_object_utils(transaction)
  
    rand oper_mode   op;
         logic tx_start, rx_start;
         logic rst;
    rand logic [7:0] tx_data;
    rand logic [16:0] baud;
    rand logic [3:0] length; 
    rand logic parity_type, parity_en;
         logic stop2;
         logic tx_done, rx_done, tx_err, rx_err;
         logic [7:0] rx_out;
  
 
  
  constraint baud_c { baud inside {4800,9600,14400,19200,38400,57600}; }
  constraint length_c { length inside {5,6,7,8}; }
 
  function new(string name = "transaction");
    super.new(name);
  endfunction
 
endclass : transaction
 
 
///////////////////////////////////////////////////////////////////////
 
 
///////////////////random baud - fixed length = 8 - parity enable - parity type : random - single stop
class rand_baud extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud)
  
  transaction tr;
 
  function new(string name = "rand_baud");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op     = rand_baud_1_stop;
        tr.length = 8;
        tr.baud   = 9600;
        tr.rst       = 1'b0;
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b1;
        tr.stop2     = 1'b0;
        finish_item(tr);
      end
  endtask
  
 
endclass
////////////////////random baud - fixed length = 8 - parity enable - parity type : random - two stop
//////////////////////////////////////////////////////////
class rand_baud_with_stop extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud_with_stop)
  
  transaction tr;
 
  function new(string name = "rand_baud_with_stop");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op        = rand_baud_2_stop;
        tr.rst       = 1'b0;
        tr.length    = 8;
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b1;
        tr.stop2     = 1'b1;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
//////////////////////////////////////////////////////////
////////////////////fixed length = 5 - variable baud - with parity
class rand_baud_len5p extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud_len5p)
  
  transaction tr;
 
  function new(string name = "rand_baud_len5p");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op     = length5wp;
        tr.rst       = 1'b0;
        tr.tx_data   = {3'b000, tr.tx_data[7:3]};
        tr.length = 5;
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b1;
        tr.stop2     = 1'b0;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
 
 
//////////////////////////////////////////////////////////
////////////////////fixed length = 6 - variable baud - with parity
class rand_baud_len6p extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud_len6p)
  
  transaction tr;
 
  function new(string name = "rand_baud_len6p");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op     = length6wp;
        tr.rst       = 1'b0;
        tr.length = 6;
        tr.tx_data   = {2'b00, tr.tx_data[7:2]};
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b1;
        tr.stop2     = 1'b0;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
//////////////////////////////////////////////////////////
////////////////////fixed length = 7 - variable baud - with parity
class rand_baud_len7p extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud_len7p)
  
  transaction tr;
 
  function new(string name = "rand_baud_len7p");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op     = length7wp;
        tr.rst       = 1'b0;
        tr.length = 7;
        tr.tx_data   = {1'b0, tr.tx_data[7:1]};
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b1;
        tr.stop2     = 1'b0;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
//////////////////////////////////////////////////////////
////////////////////fixed length = 8 - variable baud - with parity
class rand_baud_len8p extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud_len8p)
  
  transaction tr;
 
  function new(string name = "rand_baud_len8p");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op     = length8wp;
        tr.rst       = 1'b0;
        tr.length = 8;
        tr.tx_data   =  tr.tx_data[7:0];
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b1;
        tr.stop2     = 1'b0;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
//////////////////////////////////////////////////////////
////////////////////fixed length = 5 - variable baud - without parity
class rand_baud_len5 extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud_len5)
  
  transaction tr;
 
  function new(string name = "rand_baud_len5");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op     = length5wop;
        tr.rst       = 1'b0;
        tr.length = 5;
        tr.tx_data   = {3'b000, tr.tx_data[7:3]};
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b0;
        tr.stop2     = 1'b0;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
 
//////////////////////////////////////////////////////////
////////////////////fixed length = 6- variable baud - without parity
class rand_baud_len6 extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud_len6)
  
  transaction tr;
 
  function new(string name = "rand_baud_len6");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op     = length6wop;
        tr.rst       = 1'b0;
        tr.length = 6;
        tr.tx_data   = {2'b00, tr.tx_data[7:2]};
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b0;
        tr.stop2     = 1'b0;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
//////////////////////////////////////////////////////////
////////////////////fixed length = 7- variable baud - without parity
class rand_baud_len7 extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud_len7)
  
  transaction tr;
 
  function new(string name = "rand_baud_len7");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op     = length7wop;
        tr.rst       = 1'b0;
        tr.length = 7;
        tr.tx_data   = {1'b0, tr.tx_data[7:1]};
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b0;
        tr.stop2     = 1'b0;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
 
//////////////////////////////////////////////////////////
////////////////////fixed length = 8 - variable baud - without parity
class rand_baud_len8 extends uvm_sequence#(transaction);
  `uvm_object_utils(rand_baud_len8)
  
  transaction tr;
 
  function new(string name = "rand_baud_len8");
    super.new(name);
  endfunction
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize);
        tr.op     = length8wop;
        tr.rst       = 1'b0;
        tr.length = 8;
        tr.tx_data   =  tr.tx_data[7:0];
        tr.tx_start  = 1'b1;
        tr.rx_start  = 1'b1;
        tr.parity_en = 1'b0;
        tr.stop2     = 1'b0;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
///////////////////////////////////////////////////////////////////////////////////////
 
 
 
 
class driver extends uvm_driver #(transaction);
  `uvm_component_utils(driver)
  
  virtual uart_if vif;
  transaction tr;
  
  
  function new(input string path = "drv", uvm_component parent = null);
    super.new(path,parent);
  endfunction
  
 virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
     tr = transaction::type_id::create("tr");
      
   if(!uvm_config_db#(virtual uart_if)::get(this,"","vif",vif)) 
      `uvm_error("drv","Unable to access Interface");
  endfunction
  
  
  
  task reset_dut();
 
    repeat(5) 
    begin
    vif.rst      <= 1'b1;  ///active high reset
    vif.tx_start <= 1'b0;
    vif.rx_start <= 1'b0;
    vif.tx_data  <= 8'h00;
    vif.baud     <= 16'h0;
    vif.length   <= 4'h0;
    vif.parity_type <= 1'b0;
    vif.parity_en   <= 1'b0;
    vif.stop2  <= 1'b0;
   `uvm_info("DRV", "System Reset : Start of Simulation", UVM_MEDIUM);
    @(posedge vif.clk);
      end
  endtask
  
  task drive();
    reset_dut();
   forever begin
     
         seq_item_port.get_next_item(tr);
     
                                             
                            vif.rst         <= 1'b0;
                            vif.tx_start    <= tr.tx_start;
                            vif.rx_start    <= tr.rx_start;
                            vif.tx_data     <= tr.tx_data;
                            vif.baud        <= tr.baud;
                            vif.length      <= tr.length;
                            vif.parity_type <= tr.parity_type;
                            vif.parity_en   <= tr.parity_en;
                            vif.stop2       <= tr.stop2;
     `uvm_info("DRV", $sformatf("BAUD:%0d LEN:%0d PAR_T:%0d PAR_EN:%0d STOP:%0d TX_DATA:%0d", tr.baud, tr.length, tr.parity_type, tr.parity_en, tr.stop2, tr.tx_data), UVM_NONE);
                            @(posedge vif.clk); 
                            @(posedge vif.tx_done);
     @(negedge vif.rx_done);
                            
     
       seq_item_port.item_done();
     
   end
  endtask
  
 
  virtual task run_phase(uvm_phase phase);
    drive();
  endtask
 
  
endclass
 
//////////////////////////////////////////////////////////////////////////////////////////////
 
class mon extends uvm_monitor;
`uvm_component_utils(mon)
 
uvm_analysis_port#(transaction) send;
transaction tr;
virtual uart_if vif;
 
    function new(input string inst = "mon", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tr = transaction::type_id::create("tr");
    send = new("send", this);
      if(!uvm_config_db#(virtual uart_if)::get(this,"","vif",vif))//uvm_test_top.env.agent.drv.aif
        `uvm_error("MON","Unable to access Interface");
    endfunction
    
    
    virtual task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.clk);
      if(vif.rst)
        begin
          tr.rst = 1'b1;
        `uvm_info("MON", "SYSTEM RESET DETECTED", UVM_NONE);
        send.write(tr);
        end
      else
         begin
         @(posedge vif.tx_done);
         tr.rst         = 1'b0;
         tr.tx_start    = vif.tx_start;
         tr.rx_start    = vif.rx_start;
         tr.tx_data     = vif.tx_data;
         tr.baud        = vif.baud;
         tr.length      = vif.length;
         tr.parity_type = vif.parity_type;
         tr.parity_en   = vif.parity_en;
         tr.stop2       = vif.stop2;
           @(negedge vif.rx_done);
         
         tr.rx_out      = vif.rx_out;
           `uvm_info("MON", $sformatf("BAUD:%0d LEN:%0d PAR_T:%0d PAR_EN:%0d STOP:%0d TX_DATA:%0d RX_DATA:%0d", tr.baud, tr.length, tr.parity_type, tr.parity_en, tr.stop2, tr.tx_data, tr.rx_out), UVM_NONE);
          send.write(tr);
         end
    
    
    end
   endtask 
 
endclass
//////////////////////////////////////////////////////////////////////////////////////////////////
 
class sco extends uvm_scoreboard;
`uvm_component_utils(sco)
 
  uvm_analysis_imp#(transaction,sco) recv;
 
 
 
    function new(input string inst = "sco", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    recv = new("recv", this);
    endfunction
    
    
  virtual function void write(transaction tr);
    `uvm_info("SCO", $sformatf("BAUD:%0d LEN:%0d PAR_T:%0d PAR_EN:%0d STOP:%0d TX_DATA:%0d RX_DATA:%0d", tr.baud, tr.length, tr.parity_type, tr.parity_en, tr.stop2, tr.tx_data, tr.rx_out), UVM_NONE);
    if(tr.rst == 1'b1)
      `uvm_info("SCO", "System Reset", UVM_NONE)
    else if(tr.tx_data == tr.rx_out)
      `uvm_info("SCO", "Test Passed", UVM_NONE)
    else
      `uvm_info("SCO", "Test Failed", UVM_NONE)
    $display("----------------------------------------------------------------");
    endfunction
 
endclass
 
 
//////////////////////////////////////////////////////////////////////////////////////////////
                  
                  
class agent extends uvm_agent;
`uvm_component_utils(agent)
  
  uart_config cfg;
 
function new(input string inst = "agent", uvm_component parent = null);
super.new(inst,parent);
endfunction
 
 driver d;
 uvm_sequencer#(transaction) seqr;
 mon m;
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   cfg =  uart_config::type_id::create("cfg"); 
   m = mon::type_id::create("m",this);
  
  if(cfg.is_active == UVM_ACTIVE)
   begin   
   d = driver::type_id::create("d",this);
   seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
   end
  
  
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
  if(cfg.is_active == UVM_ACTIVE) begin  
    d.seq_item_port.connect(seqr.seq_item_export);
  end
endfunction
 
endclass
 
//////////////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
`uvm_component_utils(env)
 
function new(input string inst = "env", uvm_component c);
super.new(inst,c);
endfunction
 
agent a;
sco s;
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
  a = agent::type_id::create("a",this);
  s = sco::type_id::create("s", this);
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
 a.m.send.connect(s.recv);
endfunction
 
endclass
 
//////////////////////////////////////////////////////////////////////////
 
class test extends uvm_test;
`uvm_component_utils(test)
 
function new(input string inst = "test", uvm_component c);
super.new(inst,c);
endfunction
 
 
env e;
rand_baud rb;
rand_baud_with_stop rbs;
rand_baud_len5p  rb5l;
rand_baud_len6p rb6l;
rand_baud_len7p rb7l;
rand_baud_len8p rb8l;
  ///////////////////////
  
  rand_baud_len5  rb5lwop;
  rand_baud_len6  rb6lwop;
  rand_baud_len7  rb7lwop;
  rand_baud_len8  rb8lwop;
  
  
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   e       = env::type_id::create("env",this);
   rb      = rand_baud::type_id::create("rb");
   rbs     = rand_baud_with_stop::type_id::create("rbs");
  /////////////fixed length var baud with parity
   rb5l    = rand_baud_len5p::type_id::create("rb5l");
   rb6l    = rand_baud_len6p::type_id::create("rb6l");
   rb7l    = rand_baud_len7p::type_id::create("rb7l");
   rb8l    = rand_baud_len8p::type_id::create("rb8l");
  
  ///////////////fixed len var baud without parity
  rb5lwop = rand_baud_len5::type_id::create("rb5lwop");
  rb6lwop = rand_baud_len6::type_id::create("rb6lwop");
  rb7lwop = rand_baud_len7::type_id::create("rb7lwop");
  rb8lwop = rand_baud_len8::type_id::create("rb8lwop");
  
  
endfunction
 
virtual task run_phase(uvm_phase phase);
phase.raise_objection(this);
rb8l.start(e.a.seqr);
#20;
rb5lwop.start(e.a.seqr);
#20;
rb6lwop.start(e.a.seqr);
#20;
rb7lwop.start(e.a.seqr);
#20;
rb8lwop.start(e.a.seqr);
#20;
phase.drop_objection(this);
endtask
endclass
 
//////////////////////////////////////////////////////////////////////
module tb;
  
  
  uart_if vif();
  
 
  
  
  uart_top dut (.clk(vif.clk), .rst(vif.rst), .tx_start(vif.tx_start), .rx_start(vif.rx_start), .tx_data(vif.tx_data), .baud(vif.baud), .length(vif.length), .parity_type(vif.parity_type), .parity_en(vif.parity_en),.stop2(vif.stop2),.tx_done(vif.tx_done), .rx_done(vif.rx_done), .tx_err(vif.tx_err), .rx_err(vif.rx_err), .rx_out(vif.rx_out));
  
  initial begin
    vif.clk <= 0;
  end
 
  always #10 vif.clk <= ~vif.clk;
 
  
  
  initial begin
    uvm_config_db#(virtual uart_if)::set(null, "*", "vif", vif);
    run_test("test");
   end
  
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
  end
 
  
endmodule
```
## Output
```
UVM_INFO @ 0: reporter [RNTST] Running test test...
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(20867) @ 0: reporter [UVM/COMP/NAMECHECK] This implementation of the component name checks requires DPI to be enabled
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(412) @ 0: uvm_test_top.env.a.d [DRV] System Reset : Start of Simulation
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(412) @ 10000: uvm_test_top.env.a.d [DRV] System Reset : Start of Simulation
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(480) @ 10000: uvm_test_top.env.a.m [MON] SYSTEM RESET DETECTED
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 10000: uvm_test_top.env.s [SCO] BAUD:x LEN:x PAR_T:x PAR_EN:x STOP:x TX_DATA:x RX_DATA:x
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(529) @ 10000: uvm_test_top.env.s [SCO] System Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(480) @ 30000: uvm_test_top.env.a.m [MON] SYSTEM RESET DETECTED
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 30000: uvm_test_top.env.s [SCO] BAUD:x LEN:x PAR_T:x PAR_EN:x STOP:x TX_DATA:x RX_DATA:x
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(529) @ 30000: uvm_test_top.env.s [SCO] System Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(412) @ 30000: uvm_test_top.env.a.d [DRV] System Reset : Start of Simulation
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(412) @ 50000: uvm_test_top.env.a.d [DRV] System Reset : Start of Simulation
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(480) @ 50000: uvm_test_top.env.a.m [MON] SYSTEM RESET DETECTED
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 50000: uvm_test_top.env.s [SCO] BAUD:x LEN:x PAR_T:x PAR_EN:x STOP:x TX_DATA:x RX_DATA:x
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(529) @ 50000: uvm_test_top.env.s [SCO] System Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(480) @ 70000: uvm_test_top.env.a.m [MON] SYSTEM RESET DETECTED
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 70000: uvm_test_top.env.s [SCO] BAUD:x LEN:x PAR_T:x PAR_EN:x STOP:x TX_DATA:x RX_DATA:x
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(529) @ 70000: uvm_test_top.env.s [SCO] System Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(412) @ 70000: uvm_test_top.env.a.d [DRV] System Reset : Start of Simulation
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(480) @ 90000: uvm_test_top.env.a.m [MON] SYSTEM RESET DETECTED
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 90000: uvm_test_top.env.s [SCO] BAUD:x LEN:x PAR_T:x PAR_EN:x STOP:x TX_DATA:x RX_DATA:x
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(529) @ 90000: uvm_test_top.env.s [SCO] System Reset
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 90000: uvm_test_top.env.a.d [DRV] BAUD:4800 LEN:8 PAR_T:0 PAR_EN:1 STOP:0 TX_DATA:143
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 4845350000: uvm_test_top.env.a.m [MON] BAUD:4800 LEN:8 PAR_T:0 PAR_EN:1 STOP:0 TX_DATA:143 RX_DATA:143
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 4845350000: uvm_test_top.env.s [SCO] BAUD:4800 LEN:8 PAR_T:0 PAR_EN:1 STOP:0 TX_DATA:143 RX_DATA:143
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 4845350000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 4845350000: uvm_test_top.env.a.d [DRV] BAUD:38400 LEN:8 PAR_T:1 PAR_EN:1 STOP:0 TX_DATA:230
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 5512670000: uvm_test_top.env.a.m [MON] BAUD:38400 LEN:8 PAR_T:1 PAR_EN:1 STOP:0 TX_DATA:230 RX_DATA:230
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 5512670000: uvm_test_top.env.s [SCO] BAUD:38400 LEN:8 PAR_T:1 PAR_EN:1 STOP:0 TX_DATA:230 RX_DATA:230
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 5512670000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 5512670000: uvm_test_top.env.a.d [DRV] BAUD:57600 LEN:8 PAR_T:1 PAR_EN:1 STOP:0 TX_DATA:233
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 5965150000: uvm_test_top.env.a.m [MON] BAUD:57600 LEN:8 PAR_T:1 PAR_EN:1 STOP:0 TX_DATA:233 RX_DATA:233
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 5965150000: uvm_test_top.env.s [SCO] BAUD:57600 LEN:8 PAR_T:1 PAR_EN:1 STOP:0 TX_DATA:233 RX_DATA:233
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 5965150000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 5965150000: uvm_test_top.env.a.d [DRV] BAUD:9600 LEN:8 PAR_T:0 PAR_EN:1 STOP:0 TX_DATA:25
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 8685790000: uvm_test_top.env.a.m [MON] BAUD:9600 LEN:8 PAR_T:0 PAR_EN:1 STOP:0 TX_DATA:25 RX_DATA:25
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 8685790000: uvm_test_top.env.s [SCO] BAUD:9600 LEN:8 PAR_T:0 PAR_EN:1 STOP:0 TX_DATA:25 RX_DATA:25
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 8685790000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 8685790000: uvm_test_top.env.a.d [DRV] BAUD:38400 LEN:8 PAR_T:0 PAR_EN:1 STOP:0 TX_DATA:226
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 9353110000: uvm_test_top.env.a.m [MON] BAUD:38400 LEN:8 PAR_T:0 PAR_EN:1 STOP:0 TX_DATA:226 RX_DATA:226
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 9353110000: uvm_test_top.env.s [SCO] BAUD:38400 LEN:8 PAR_T:0 PAR_EN:1 STOP:0 TX_DATA:226 RX_DATA:226
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 9353110000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 9353130000: uvm_test_top.env.a.d [DRV] BAUD:9600 LEN:5 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:1
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 11236630000: uvm_test_top.env.a.m [MON] BAUD:9600 LEN:5 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:1 RX_DATA:1
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 11236630000: uvm_test_top.env.s [SCO] BAUD:9600 LEN:5 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:1 RX_DATA:1
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 11236630000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 11236630000: uvm_test_top.env.a.d [DRV] BAUD:38400 LEN:5 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:18
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 11694790000: uvm_test_top.env.a.m [MON] BAUD:38400 LEN:5 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:18 RX_DATA:18
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 11694790000: uvm_test_top.env.s [SCO] BAUD:38400 LEN:5 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:18 RX_DATA:18
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 11694790000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 11694790000: uvm_test_top.env.a.d [DRV] BAUD:14400 LEN:5 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:10
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 12956230000: uvm_test_top.env.a.m [MON] BAUD:14400 LEN:5 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:10 RX_DATA:10
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 12956230000: uvm_test_top.env.s [SCO] BAUD:14400 LEN:5 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:10 RX_DATA:10
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 12956230000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 12956230000: uvm_test_top.env.a.d [DRV] BAUD:19200 LEN:5 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:21
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 13893430000: uvm_test_top.env.a.m [MON] BAUD:19200 LEN:5 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:21 RX_DATA:21
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 13893430000: uvm_test_top.env.s [SCO] BAUD:19200 LEN:5 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:21 RX_DATA:21
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 13893430000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 13893430000: uvm_test_top.env.a.d [DRV] BAUD:4800 LEN:5 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:17
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 17680830000: uvm_test_top.env.a.m [MON] BAUD:4800 LEN:5 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:17 RX_DATA:17
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 17680830000: uvm_test_top.env.s [SCO] BAUD:4800 LEN:5 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:17 RX_DATA:17
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 17680830000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 17680850000: uvm_test_top.env.a.d [DRV] BAUD:38400 LEN:6 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:44
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 18188790000: uvm_test_top.env.a.m [MON] BAUD:38400 LEN:6 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:44 RX_DATA:44
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 18188790000: uvm_test_top.env.s [SCO] BAUD:38400 LEN:6 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:44 RX_DATA:44
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 18188790000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 18188790000: uvm_test_top.env.a.d [DRV] BAUD:57600 LEN:6 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:6
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 18535990000: uvm_test_top.env.a.m [MON] BAUD:57600 LEN:6 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:6 RX_DATA:6
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 18535990000: uvm_test_top.env.s [SCO] BAUD:57600 LEN:6 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:6 RX_DATA:6
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 18535990000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 18535990000: uvm_test_top.env.a.d [DRV] BAUD:57600 LEN:6 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:0
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 18883190000: uvm_test_top.env.a.m [MON] BAUD:57600 LEN:6 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:0 RX_DATA:0
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 18883190000: uvm_test_top.env.s [SCO] BAUD:57600 LEN:6 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:0 RX_DATA:0
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 18883190000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 18883190000: uvm_test_top.env.a.d [DRV] BAUD:19200 LEN:6 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:17
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 19932590000: uvm_test_top.env.a.m [MON] BAUD:19200 LEN:6 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:17 RX_DATA:17
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 19932590000: uvm_test_top.env.s [SCO] BAUD:19200 LEN:6 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:17 RX_DATA:17
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 19932590000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 19932590000: uvm_test_top.env.a.d [DRV] BAUD:9600 LEN:6 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:62
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 22025390000: uvm_test_top.env.a.m [MON] BAUD:9600 LEN:6 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:62 RX_DATA:62
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 22025390000: uvm_test_top.env.s [SCO] BAUD:9600 LEN:6 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:62 RX_DATA:62
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 22025390000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 22025410000: uvm_test_top.env.a.d [DRV] BAUD:4800 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:103
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 26622510000: uvm_test_top.env.a.m [MON] BAUD:4800 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:103 RX_DATA:103
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 26622510000: uvm_test_top.env.s [SCO] BAUD:4800 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:103 RX_DATA:103
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 26622510000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 26622510000: uvm_test_top.env.a.d [DRV] BAUD:9600 LEN:7 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:21
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 28898430000: uvm_test_top.env.a.m [MON] BAUD:9600 LEN:7 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:21 RX_DATA:21
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 28898430000: uvm_test_top.env.s [SCO] BAUD:9600 LEN:7 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:21 RX_DATA:21
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 28898430000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 28898430000: uvm_test_top.env.a.d [DRV] BAUD:57600 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:10
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 29276990000: uvm_test_top.env.a.m [MON] BAUD:57600 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:10 RX_DATA:10
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 29276990000: uvm_test_top.env.s [SCO] BAUD:57600 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:10 RX_DATA:10
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 29276990000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 29276990000: uvm_test_top.env.a.d [DRV] BAUD:9600 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:46
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 31579070000: uvm_test_top.env.a.m [MON] BAUD:9600 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:46 RX_DATA:46
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 31579070000: uvm_test_top.env.s [SCO] BAUD:9600 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:46 RX_DATA:46
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 31579070000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 31579070000: uvm_test_top.env.a.d [DRV] BAUD:19200 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:6
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 32727470000: uvm_test_top.env.a.m [MON] BAUD:19200 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:6 RX_DATA:6
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 32727470000: uvm_test_top.env.s [SCO] BAUD:19200 LEN:7 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:6 RX_DATA:6
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 32727470000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 32727490000: uvm_test_top.env.a.d [DRV] BAUD:4800 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:167
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 37742510000: uvm_test_top.env.a.m [MON] BAUD:4800 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:167 RX_DATA:167
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 37742510000: uvm_test_top.env.s [SCO] BAUD:4800 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:167 RX_DATA:167
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 37742510000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 37742510000: uvm_test_top.env.a.d [DRV] BAUD:4800 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:70
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 42757550000: uvm_test_top.env.a.m [MON] BAUD:4800 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:70 RX_DATA:70
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 42757550000: uvm_test_top.env.s [SCO] BAUD:4800 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:70 RX_DATA:70
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 42757550000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 42757550000: uvm_test_top.env.a.d [DRV] BAUD:9600 LEN:8 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:12
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 45229670000: uvm_test_top.env.a.m [MON] BAUD:9600 LEN:8 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:12 RX_DATA:12
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 45229670000: uvm_test_top.env.s [SCO] BAUD:9600 LEN:8 PAR_T:0 PAR_EN:0 STOP:0 TX_DATA:12 RX_DATA:12
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 45229670000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 45229670000: uvm_test_top.env.a.d [DRV] BAUD:9600 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:95
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 47727950000: uvm_test_top.env.a.m [MON] BAUD:9600 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:95 RX_DATA:95
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 47727950000: uvm_test_top.env.s [SCO] BAUD:9600 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:95 RX_DATA:95
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 47727950000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(433) @ 47727950000: uvm_test_top.env.a.d [DRV] BAUD:38400 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:40
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(498) @ 48345470000: uvm_test_top.env.a.m [MON] BAUD:38400 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:40 RX_DATA:40
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(527) @ 48345470000: uvm_test_top.env.s [SCO] BAUD:38400 LEN:8 PAR_T:1 PAR_EN:0 STOP:0 TX_DATA:40 RX_DATA:40
UVM_INFO C:/eng_apps/vivado_projects/uart/uart/uart.srcs/sim_1/new/tb.sv(531) @ 48345470000: uvm_test_top.env.s [SCO] Test Passed
----------------------------------------------------------------
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(19968) @ 48345490000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase
UVM_INFO C:/Xilinx/Vivado/2023.2/data/system_verilog/uvm_1.2/xlnx_uvm_package.sv(13673) @ 48345490000: reporter [UVM/REPORT/SERVER] 
--- UVM Report Summary ---
```
