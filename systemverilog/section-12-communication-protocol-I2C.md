# Communication protocol: verification of I2C (inter-integrated circuit)
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/48c9d61d-d117-4a02-a1c5-bfec7228ddcf)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/9e15839d-9800-4128-bfb7-0713ecbf30ff)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/eebc8588-96bb-4196-ae38-6dcf579c2db9)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/487f6e05-a886-4794-9415-021d242ed68e)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/02d905a8-3dc7-4de4-bb07-dadf3c474907)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/74bff902-e932-4141-9f46-92840d455d29)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/2236d97d-b6da-49d5-b2e0-e31d93b79f55)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f4434f23-2d3c-4d77-9f0d-be8f7e43a213)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/36b00854-f40e-4baf-b0d8-7ad2e5535b4d)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0ea6e33c-5369-42f4-883c-c8a33636d309)

```
/////////// Master
 
`timescale 1ns / 1ps
 
module i2c_master( input clk, rst , newd,
input [6:0] addr,
input op,//1-r
inout sda,
output scl,
input [7:0] din,
output [7:0] dout,
output reg busy, ack_err, done
);
 
reg scl_t = 0;
reg sda_t = 0;
 
parameter sys_freq = 40000000; //40 MHz
parameter i2c_freq = 100000;  //// 100k
 
 
parameter clk_count4 = (sys_freq/i2c_freq);/// 400
parameter clk_count1 = clk_count4/4; ///100
 
integer count1 = 0;
reg i2c_clk = 0;
 
///////4x clock
reg [1:0] pulse = 0;
always@(posedge clk)
begin
      if(rst)
       begin
       pulse <= 0;
       count1 <= 0;
       end
       else if (busy == 1'b0) ///pulse count start only after newd
        begin
        pulse <= 0;
        count1 <= 0;
        end
      else if(count1  == clk_count1 - 1)
       begin
       pulse <= 1;
       count1 <= count1 + 1;
       end
      else if(count1  == clk_count1*2 - 1)
       begin
       pulse <= 2;
       count1 <= count1 + 1;
       end
      else if(count1  == clk_count1*3 - 1)
       begin
       pulse <= 3;
       count1 <= count1 + 1;
       end
      else if(count1  == clk_count1*4 - 1)
       begin
       pulse <= 0;
       count1 <= 0;
       end
      else
       begin
       count1 <= count1 + 1;
       end
end
 
//////////////////
reg [3:0] bitcount = 0;
reg [7:0] data_addr   = 0, data_tx = 0;
reg r_ack = 0;
reg [7:0] rx_data = 0;
reg sda_en = 0;
 
 
typedef enum logic [3:0] {idle = 0, start = 1, write_addr = 2, ack_1 = 3, write_data = 4, read_data = 5, stop = 6, ack_2 =7, master_ack = 8} state_type;
state_type state = idle;
 
always@(posedge clk)
begin
 if(rst)
   begin
    bitcount   <= 0;
    data_addr  <= 0;
    data_tx    <= 0;
    scl_t <= 1;
    sda_t <= 1;
    state <= idle;
    busy  <= 1'b0;
    ack_err <= 1'b0;
    done    <= 1'b0;
   end
else
   begin
                case(state)
                
                //////////////idle state
                      idle:
                      begin
                            done  <= 1'b0;
                            if(newd == 1'b1)
                               begin
                               data_addr  <= {addr,op};
                               data_tx    <= din;
                               busy  <= 1'b1;
                               state <= start;
                               ack_err <= 1'b0;
                               end
                            else
                               begin
                               data_addr  <= 0;
                               data_tx    <= 0;
                               busy  <= 1'b0;
                               state <= idle;
                               ack_err <= 1'b0;
                               end
                      end
                  /////////////////////////////////////////////////////    
                     start: 
                     begin
                         sda_en <= 1'b1; ///send start to slave
                         case(pulse)
                         0: begin scl_t <= 1'b1; sda_t <= 1'b1; end
                         1: begin scl_t <= 1'b1; sda_t <= 1'b1; end
                         2: begin scl_t <= 1'b1; sda_t <= 1'b0; end
                         3: begin scl_t <= 1'b1; sda_t <= 1'b0; end
                         endcase
                         
                             if(count1  == clk_count1*4 - 1)
                             begin
                                state <= write_addr;
                                scl_t <= 1'b0;
                             end
                             else
                                state <= start;
                     end
                 ///////////////////////////////////////////     
                   write_addr: 
                   begin
                      sda_en <= 1'b1;  ///send addr to slave
                      if(bitcount <= 7)
                         begin
                                 case(pulse)
                                 0: begin scl_t <= 1'b0; sda_t <= 1'b0; end
                                 1: begin scl_t <= 1'b0; sda_t <= data_addr[7 - bitcount]; end
                                 2: begin scl_t <= 1'b1;  end
                                 3: begin scl_t <= 1'b1;  end
                                 endcase
                                 if(count1  == clk_count1*4 - 1)
                                 begin
                                    state <= write_addr;
                                    scl_t <= 1'b0;
                                    bitcount <= bitcount + 1;
                                 end
                                 else
                                 begin
                                    state <= write_addr;
                                 end
                             
                         end
                      else
                        begin
                        state <= ack_1;
                        bitcount <= 0;
                        sda_en <= 1'b0;
                        end
                   end   
                   
                   
                   //////////////////////////////////////
                   
                   ack_1 : 
                   begin
                        sda_en <= 1'b0; ///recv ack from slave
                                case(pulse)
                                 0: begin scl_t <= 1'b0; sda_t <= 1'b0; end
                                 1: begin scl_t <= 1'b0; sda_t <= 1'b0; end
                                 2: begin scl_t <= 1'b1; sda_t <= 1'b0; r_ack <= sda; end ///recv ack from slave
                                 3: begin scl_t <= 1'b1;  end
                                 endcase
                   
                       if(count1  == clk_count1*4 - 1)
                                  begin
                                      if(r_ack == 1'b0 && data_addr[0] == 1'b0)
                                        begin
                                        state <= write_data;
                                        sda_t <= 1'b0;
                                        sda_en <= 1'b1; /////write data to slave
                                        bitcount <= 0;
                                        end
                                      else if (r_ack == 1'b0 && data_addr[0] == 1'b1)
                                      begin
                                        state <= read_data;
                                        sda_t <= 1'b1;
                                        sda_en <= 1'b0; ///read data from slave
                                        bitcount <= 0;
                                      end
                                      else
                                      begin
                                        state <= stop;
                                        sda_en <= 1'b1; ////send stop to slave
                                        ack_err <= 1'b1;
                                      end
                                  end
                                 else
                                  begin
                                    state <= ack_1;
                                  end
                     
                   end
                   
                 write_data: 
                 begin
                   ///write data to slave
                  if(bitcount <= 7)
                         begin
                                 case(pulse)
                                 0: begin scl_t <= 1'b0;   end
                                 1: begin scl_t <= 1'b0;sda_en <= 1'b1; sda_t <= data_tx[7 - bitcount];                                  end
                                 2: begin scl_t <= 1'b1;  end
                                 3: begin scl_t <= 1'b1;  end
                                 endcase
                                 if(count1  == clk_count1*4 - 1)
                                 begin
                                    state <= write_data;
                                    scl_t <= 1'b0;
                                    bitcount <= bitcount + 1;
                                 end
                                 else
                                 begin
                                    state <= write_data;
                                 end
                             
                         end
                      else
                        begin
                        state <= ack_2;
                        bitcount <= 0;
                        sda_en <= 1'b0; ///read from slave
                        end
                 
                 
                 end 
                 ///////////////////////////// read_data
                 
                 read_data: 
                 begin
                 sda_en <= 1'b0; ///read from slave
                 if(bitcount <= 7)
                         begin
                                 case(pulse)
                                 0: begin scl_t <= 1'b0; sda_t <= 1'b0; end
                                 1: begin scl_t <= 1'b0; sda_t <= 1'b0; end
                                 2: begin scl_t <= 1'b1; rx_data[7:0] <= (count1 == 200) ? {rx_data[6:0],sda} : rx_data; end
                                 3: begin scl_t <= 1'b1;  end
                                 endcase
                                 if(count1  == clk_count1*4 - 1)
                                 begin
                                    state <= read_data;
                                    scl_t <= 1'b0;
                                    bitcount <= bitcount + 1;
                                 end
                                 else
                                 begin
                                    state <= read_data;
                                 end
                             
                         end
                      else
                        begin
                        state <= master_ack;
                        bitcount <= 0;
                        sda_en <= 1'b1; ///master will send ack to slave
                        end
                 
                 
                 
                 end
                 ////////////////////master ack -> send nack
                 master_ack : 
                   begin
                      sda_en <= 1'b1;
                      
                                case(pulse)
                                 0: begin scl_t <= 1'b0; sda_t <= 1'b1; end
                                 1: begin scl_t <= 1'b0; sda_t <= 1'b1; end
                                 2: begin scl_t <= 1'b1; sda_t <= 1'b1; end 
                                 3: begin scl_t <= 1'b1; sda_t <= 1'b1; end
                                 endcase
                   
                       if(count1  == clk_count1*4 - 1)
                                  begin
                                      sda_t <= 1'b0;
                                      state <= stop;
                                      sda_en <= 1'b1; ///send stop to slave
                                      
                                  end
                                 else
                                  begin
                                    state <= master_ack;
                                  end
                     
                   end
                 
                 
                 
                 /////////////////ack 2
                 
                  ack_2 : 
                   begin
                     sda_en <= 1'b0; ///recv ack from slave
                                case(pulse)
                                 0: begin scl_t <= 1'b0; sda_t <= 1'b0; end
                                 1: begin scl_t <= 1'b0; sda_t <= 1'b0; end
                                 2: begin scl_t <= 1'b1; sda_t <= 1'b0; r_ack <= sda; end ///recv ack from slave
                                 3: begin scl_t <= 1'b1;  end
                                 endcase
                   
                       if(count1  == clk_count1*4 - 1)
                                  begin
                                      sda_t <= 1'b0;
                                      sda_en <= 1'b1; ///send stop to slave
                                      if(r_ack == 1'b0 )
                                        begin
                                        state <= stop;
                                        ack_err <= 1'b0;
                                        end
                                      else
                                        begin
                                        state <= stop;
                                        ack_err <= 1'b1;
                                        end
                                  end
                                 else
                                  begin
                                    state <= ack_2;
                                  end
                     
                   end
 
                /////////////////////////////////////////////stop  
                   stop: 
                     begin
                     sda_en <= 1'b1; ///send stop to slave
                         case(pulse)
                         0: begin scl_t <= 1'b1; sda_t <= 1'b0; end
                         1: begin scl_t <= 1'b1; sda_t <= 1'b0; end
                         2: begin scl_t <= 1'b1; sda_t <= 1'b1; end
                         3: begin scl_t <= 1'b1; sda_t <= 1'b1; end
                         endcase
                         
                             if(count1  == clk_count1*4 - 1)
                             begin
                                state <= idle;
                                scl_t <= 1'b0;
                                busy <= 1'b0;
                                sda_en <= 1'b1; ///send start to slave
                                done   <= 1'b1;
                             end
                             else
                                state <= stop;
                     end
                     
                     //////////////////////////////////////////////
                      
                 default : state <= idle;
               endcase
   end
end
 
assign sda = (sda_en == 1) ? (sda_t == 0) ? 1'b0 : 1'b1 : 1'bz; /// en = 1 -> write to slave else read
////// if sda_en == 1 then if sda_t == 0 pull line low else release so that pull up make line high
/*
if(sda_en)
   if(!sda_t)
      sda = 0
   else
      sda = z
else
   sda = z
*/
assign scl = scl_t;
assign dout = rx_data;
endmodule
 
 
///////////////////// Slave
`timescale 1ns / 1ps
 
module i2c_Slave(
input scl,clk,rst,
inout sda,
output reg ack_err, done
    );
  
typedef enum logic [3:0] {idle = 0, read_addr = 1, send_ack1 = 2, send_data = 3, master_ack = 4, read_data = 5, send_ack2 = 6, wait_p = 7, detect_stop = 8} state_type;
state_type state = idle;    
 
reg [7:0] mem [128];
reg [7:0] r_addr;
reg [6:0] addr;
reg r_mem = 0;
reg w_mem = 0;
reg [7:0] dout;
reg [7:0] din;
reg sda_t;
reg sda_en;
reg [3:0] bitcnt = 0;
 
 
 
 
///////////// initialize mem
always@(posedge clk)
begin
  if(rst)
  begin
      for(int i = 0 ; i < 128; i++)
        begin
        mem[i] = i;
        end
      dout <= 8'h0;
  end
  else if (r_mem == 1'b1)
   begin
      dout <= mem[addr];
   end
  else if (w_mem == 1'b1)
   begin
      mem[addr] <= din;
   end 
   
end
 
/////////////////////////pulse_gen logic
parameter sys_freq = 40000000;
parameter i2c_freq = 100000;
 
 
parameter clk_count4 = (sys_freq/i2c_freq);
parameter clk_count1 = clk_count4/4;
integer count1 = 0;
reg i2c_clk = 0;
 
///////4x clock
reg [1:0] pulse = 0;
reg busy;
always@(posedge clk)
begin
      if(rst)
      begin
        pulse <= 0;
        count1 <= 0;
      end
      else if(busy == 1'b0)
       begin
       pulse <= 2;
       count1 <= 202;
       end
      else if(count1  == clk_count1 - 1)
       begin
       pulse <= 1;
       count1 <= count1 + 1;
       end
      else if(count1  == clk_count1*2 - 1)
       begin
       pulse <= 2;
       count1 <= count1 + 1;
       end
      else if(count1  == clk_count1*3 - 1)
       begin
       pulse <= 3;
       count1 <= count1 + 1;
       end
      else if(count1  == clk_count1*4 - 1)
       begin
       pulse <= 0;
       count1 <= 0;
       end
      else
       begin
       count1 <= count1 + 1;
       end
end
 
 
 
 
 
reg scl_t;
wire start;
always@(posedge clk)
begin
scl_t <= scl;
end
 
assign start = ~scl & scl_t; 
 
reg r_ack;
 
always@(posedge clk)
begin
if(rst)
 begin
                  bitcnt <= 0;
                  state  <= idle;
                  r_addr <= 7'b0000000;
                  sda_en <= 1'b0;
                  sda_t <= 1'b0;
                  addr  <= 0;
                  r_mem <= 0;
                  din   <= 8'h00; 
                  ack_err <= 0;
                  done    <= 1'b0;
                  busy <= 1'b0;
 end
 
 else
    begin
      case(state)
               idle: begin
                   if(scl == 1'b1 && sda == 1'b0)
                    begin
                    busy <= 1'b1;
                    state <= wait_p; 
                    end
                   else
                    begin
                    state <= idle;
                    end
               end
               //////////////////////
               wait_p :  
               begin
                if (pulse == 2'b11 && count1 == 399)
                    state <= read_addr;
                else
                    state <= wait_p;
               
               end
               /////////////////////////////////////
               read_addr: 
               begin
                         sda_en <= 1'b0;  ///read addr to slave
                              if(bitcnt <= 7)
                                 begin
                                         case(pulse)
                                         0: begin  end
                                         1: begin  end
                                         2: begin   r_addr <= (count1 == 200) ? {r_addr[6:0],sda} : r_addr; end 
                                         3: begin  end
                                         endcase
                                         if(count1  == clk_count1*4 - 1)
                                         begin
                                            state <= read_addr;
                                            bitcnt <= bitcnt + 1;
                                         end
                                         else
                                         begin
                                            state <= read_addr;
                                         end
                                     
                                 end
                              else
                                begin
                                state  <= send_ack1;
                                bitcnt <= 0;
                                sda_en <= 1'b1;
                                addr <= r_addr[7:1];
                                end
                       
                      end
                      /////////////////////////// send ack
                      
                      send_ack1: 
                      begin
                                    case(pulse)
                                         0: begin  sda_t <= 1'b0; end
                                         1: begin  end
                                         2: begin  end 
                                         3: begin  end
                                     endcase
                                  if(count1  == clk_count1*4 - 1)
                                       begin
                                          if(r_addr[0] == 1'b1) //read
                                            begin
                                            state <= send_data;
                                            r_mem <= 1'b1;
                                            end
                                          else
                                            begin
                                             state <= read_data;
                                             r_mem <= 1'b0;
                                            end
                                         end
                                  else
                                       begin
                                       state <= send_ack1;
                                       end
                                    
                                    
                      end
                      
                      
                      ///////////////////////read data
                      
                       read_data: 
                        begin
                          sda_en <= 1'b0;  ///read addr to slave
                              if(bitcnt <= 7)
                                 begin
                                         case(pulse)
                                         0: begin  end
                                         1: begin  end
                                         2: begin   din <= (count1 == 200) ? {din[6:0],sda} : din; end 
                                         3: begin  end
                                         endcase
                                         if(count1  == clk_count1*4 - 1)
                                         begin
                                            state <= read_data;
                                            bitcnt <= bitcnt + 1;
                                         end
                                         else
                                         begin
                                            state <= read_data;
                                         end
                                     
                                 end
                              else
                                begin
                                state  <= send_ack2;
                                bitcnt <= 0;
                                sda_en <= 1'b1;
                                w_mem  <= 1'b1;
                                end
                       
                      end
                      /////////////////////////////////////////////
                      send_ack2: 
                      begin
                                   
                                   case(pulse)
                                         0: begin  sda_t <= 1'b0; end
                                         1: begin  w_mem <= 1'b0; end
                                         2: begin  end 
                                         3: begin  end
                                     endcase
                                  if(count1  == clk_count1*4 - 1)
                                         begin
                                          state <= detect_stop;
                                          sda_en <= 1'b0;
                                         end
                                  else
                                       begin
                                       state <= send_ack2;
                                       end
                      end
                 /////////////
                 send_data : begin
                     sda_en <= 1'b1;  ///read addr to slave
                              if(bitcnt <= 7)
                                 begin
                                         r_mem  <= 1'b0;
                                         case(pulse)
                                         0: begin    end
                                         1: begin sda_t <= (count1 == 100) ? dout[7 - bitcnt] : sda_t; end
                                         2: begin    end 
                                         3: begin    end
                                         endcase
                                         if(count1  == clk_count1*4 - 1)
                                         begin
                                            state <= send_data;
                                            bitcnt <= bitcnt + 1;
                                         end
                                         else
                                         begin
                                            state <= send_data;
                                         end
                                     
                                 end
                              else
                                begin
                                state  <= master_ack;
                                bitcnt <= 0;
                                sda_en <= 1'b0;
                                end
                     end  
                   //////////////////////////
                   master_ack: 
                   begin
                                   case(pulse)
                                         0: begin  end
                                         1: begin  end
                                         2: begin r_ack <= (count1 == 200) ? sda : r_ack; end 
                                         3: begin  end
                                     endcase
                                  if(count1  == clk_count1*4 - 1)
                                         begin
                                               if(r_ack == 1'b1) ///nack
                                                   begin
                                                   ack_err <= 1'b0;
                                                   state <= detect_stop;
                                                   sda_en <= 1'b0;
                                                   end
                                               else
                                                    begin
                                                    ack_err <= 1'b1;
                                                    state   <= detect_stop;
                                                    sda_en <= 1'b0;
                                                    end
                                         end
                                  else
                                       begin
                                       state <= master_ack;
                                       end
                      end
                   /////////////////////////////////////////
                  
                   detect_stop: 
                   begin
                       if(pulse == 2'b11 && count1 == 399)
                           begin
                           state <= idle;
                           busy <= 1'b0;
                           done <= 1'b1;
                          end
                         else
                           state <= detect_stop;
                        
                   end
                   
                 
             
      
      default: state <= idle;
      
      endcase
    end
end
 
assign sda = (sda_en == 1'b1) ? sda_t : 1'bz;
 
endmodule
 
////////////////top
 
`timescale 1ns / 1ps
 
module i2c_top(
  input clk, rst, newd, op,
  input [6:0] addr,
  input [7:0] din,
  output [7:0] dout,
  output busy,ack_err,
  output done
  );
  wire sda, scl;
  wire ack_errm, ack_errs;


  i2c_master master (clk, rst, newd, addr, op, sda, scl, din, dout, busy, ack_errm , done);
  i2c_Slave slave (scl, clk, rst, sda, ack_errs, );

  assign ack_err = ack_errs | ack_errm;
 
 
endmodule
 
///////////////////////////////////////////////////////
interface i2c_if;
  
  logic clk;
  logic rst;
  logic newd;
  logic op;   
  logic [7:0] din;
  logic [6:0] addr;
  logic [7:0] dout;
  logic  done;
  logic busy, ack_err;  
  
endinterface
```
```
class transaction;
  bit newd;
  rand bit op;
  rand bit [7:0] din;
  rand bit [6:0] addr;
  bit [7:0] dout;
  bit done;
  bit busy;
  bit ack_err;
  
  constraint addr_c {addr > 1; addr < 5; din > 1; din < 10; } 
  
  constraint rd_wr_c {
    op dist {0 :/ 50, 1 :/ 50}; 
  }
endclass

////////////////////

class generator;
  transaction trans;
  mailbox #(transaction) mbxgd;
  
  event done;  // gen completed sending requested no. of transaction
  event drvnext;  // dr complete its work
  event sconext;  // scoreboard complete its work
  
  int count = 0;
  
  function new(mailbox #(transaction) mbxgd);
    this.mbxgd = mbxgd;
    trans = new();
  endfunction
  
  task run();
    repeat(count) begin
      assert(trans.randomize) else $error("RANDOMIZATION FAILED");
      mbxgd.put(trans);
      $display("[GEN]: op : %0d, addr : %0d, din : %0d", trans.op, trans.addr, trans.din);
      @(drvnext);
      @(sconext);
    end
    -> done;
  endtask
endclass

////////////////////

class driver;
  virtual i2c_if vif;
  transaction trans;
  mailbox #(transaction) mbxgd;
  
  event drvnext;
  
  function new(mailbox #(transaction) mbxgd);
    this.mbxgd = mbxgd;
  endfunction
  
  // Resetting system
  task reset();
    vif.rst <= 1'b1;
    vif.newd <= 1'b0;
    vif.op <= 1'b0;
    vif.din <= 0;
    vif.addr <= 0;
    repeat(10) @(posedge vif.clk);
    vif.rst <= 1'b0;
    $display("[DRV] : RESET DONE");
    $display("--------------------------");
  endtask
  
  task write();
    vif.rst <= 1'b0;
    vif.newd <= 1'b1;
    vif.op <= 1'b0;
    vif.din <= $urandom;
    vif.addr <= trans.addr;
    repeat(5) @(posedge vif.clk);
    vif.newd <= 1'b0;
    @(posedge vif.done);
    $display("[DRV] : op : wr, addr : %0d, din : %0d", trans.addr, trans.din);
    vif.newd <= 1'b0;
  endtask
  
  task read();
    vif.rst <= 1'b0;
    vif.newd <= 1'b1;
    vif.op <= 1'b1;
    vif.din <= 0;
    vif.addr <= trans.addr;
    repeat(5) @(posedge vif.clk);
    vif.newd <= 1'b0;
    @(posedge vif.done);
    $display("[DRV] : op : rd, addr : %0d, dout : %0d", trans.addr, vif.dout);
  endtask
  
  task run();
    trans = new();
    forever begin
      mbxgd.get(trans);
      if (trans.op == 1'b0)
        write();
      else
        read();
      -> drvnext;
    end
  endtask
endclass

////////////////////

class monitor;
  virtual i2c_if vif;
  transaction trans;
  mailbox #(transaction) mbxms;
  
  function new(mailbox #(transaction) mbxms);
    this.mbxms= mbxms;
  endfunction
  
  task run();
    trans = new();
    
    forever begin
      @(posedge vif.done);
      trans.din = vif.din;
      trans.addr = vif.addr;
      trans.op = vif.op;
      trans.dout = vif.dout;
      repeat(5) @(posedge vif.clk);
      mbxms.put(trans);
      $display("[MON] op : %0d, addr : %0d, din : %0d, dout : %0d", trans.op, trans.addr, trans.din, trans.dout);
    end
  endtask
endclass

////////////////////

class scoreboard;
  transaction trans;
  mailbox #(transaction) mbxms;
  
  event sconext;
  
  bit [7:0] temp;
  bit [7:0] mem[128] = '{default:0};
  
  function new(mailbox #(transaction) mbxms);
    this.mbxms= mbxms;
    for (int i = 0; i < 128; i++) begin
      mem[i] <= i;
    end
  endfunction
  
  task run();
    forever begin
      mbxms.get(trans);
      temp = mem[trans.addr];
      
      if (trans.op == 1'b0) begin
        mem[trans.addr] = trans.din;
        $display("[SCO] : DATA STORED -> ADDR : %0d DATA : %0d", trans.addr, trans.din);
        $display("--------------------------");
      end
      else begin
        if ( (trans.dout == temp) /*|| (trans.dout == trans.addr) */) begin
          $display("[SCO] : DATA READ -> DATA MATCHED EXP: %0d REC: %0d", temp, trans.dout);          
        end
        else begin
          $display("[SCO] : DATA READ -> DATA MISMATCHED EXP: %0d REC: %0d", temp, trans.dout);
        end
        $display("--------------------------");
      end
      -> sconext;
    end
  endtask
endclass

////////////////////

module tb;
  generator gen;
  driver drv;
  monitor mon;
  scoreboard sco;
  
  event nextgd;
  event nextgs;
  
  mailbox #(transaction) mbxgd, mbxms;
  
  i2c_if vif();
  
  i2c_top dut (vif.clk, vif.rst, vif.newd, vif.op, vif.addr, vif.din, vif.dout, vif.busy, vif.ack_err, vif.done);
  
  initial begin
    vif.clk <= 0;
  end
  
  always #5 vif.clk <= ~vif.clk;
  
  initial begin
    mbxgd = new();
    mbxms = new();
    
    gen = new(mbxgd);
    drv = new(mbxgd);
    
    mon = new(mbxms);
    sco = new(mbxms);
    
    gen.count = 10;
    
    drv.vif = vif;
    mon.vif = vif;
    
    gen.drvnext = nextgd;
    drv.drvnext = nextgd;
    
    gen.sconext = nextgs;
    sco.sconext = nextgs;
  end
  
  task pre_test;
    drv.reset();
  endtask
  
  task test;
    fork
      gen.run();
      drv.run();
      mon.run();
      sco.run();
    join_any
  endtask
  
  task post_test;
    wait(gen.done.triggered);
    $finish();
  endtask
  
  task run();
    pre_test;
    test;
    post_test;
  endtask
  
  initial begin
    run();
  end
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars();
  end
endmodule
```
```
# KERNEL: [DRV] : RESET DONE
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 1, addr : 3, din : 7
# KERNEL: [DRV] : op : rd, addr : 3, dout : 3
# KERNEL: [MON] op : 1, addr : 3, din : 0, dout : 3
# KERNEL: [SCO] : DATA READ -> DATA MATCHED EXP: 3 REC: 3
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 0, addr : 3, din : 4
# KERNEL: [DRV] : op : wr, addr : 3, din : 4
# KERNEL: [MON] op : 0, addr : 3, din : 30, dout : 3
# KERNEL: [SCO] : DATA STORED -> ADDR : 3 DATA : 30
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 1, addr : 4, din : 2
# KERNEL: [DRV] : op : rd, addr : 4, dout : 4
# KERNEL: [MON] op : 1, addr : 4, din : 0, dout : 4
# KERNEL: [SCO] : DATA READ -> DATA MATCHED EXP: 4 REC: 4
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 1, addr : 2, din : 3
# KERNEL: [DRV] : op : rd, addr : 2, dout : 2
# KERNEL: [MON] op : 1, addr : 2, din : 0, dout : 2
# KERNEL: [SCO] : DATA READ -> DATA MATCHED EXP: 2 REC: 2
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 0, addr : 4, din : 9
# KERNEL: [DRV] : op : wr, addr : 4, din : 9
# KERNEL: [MON] op : 0, addr : 4, din : 180, dout : 2
# KERNEL: [SCO] : DATA STORED -> ADDR : 4 DATA : 180
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 1, addr : 3, din : 4
# KERNEL: [DRV] : op : rd, addr : 3, dout : 30
# KERNEL: [MON] op : 1, addr : 3, din : 0, dout : 30
# KERNEL: [SCO] : DATA READ -> DATA MATCHED EXP: 30 REC: 30
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 1, addr : 4, din : 2
# KERNEL: [DRV] : op : rd, addr : 4, dout : 180
# KERNEL: [MON] op : 1, addr : 4, din : 0, dout : 180
# KERNEL: [SCO] : DATA READ -> DATA MATCHED EXP: 180 REC: 180
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 1, addr : 4, din : 4
# KERNEL: [DRV] : op : rd, addr : 4, dout : 180
# KERNEL: [MON] op : 1, addr : 4, din : 0, dout : 180
# KERNEL: [SCO] : DATA READ -> DATA MATCHED EXP: 180 REC: 180
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 1, addr : 3, din : 6
# KERNEL: [DRV] : op : rd, addr : 3, dout : 30
# KERNEL: [MON] op : 1, addr : 3, din : 0, dout : 30
# KERNEL: [SCO] : DATA READ -> DATA MATCHED EXP: 30 REC: 30
# KERNEL: --------------------------
# KERNEL: [GEN]: op : 1, addr : 2, din : 3
# KERNEL: [DRV] : op : rd, addr : 2, dout : 2
# KERNEL: [MON] op : 1, addr : 2, din : 0, dout : 2
# KERNEL: [SCO] : DATA READ -> DATA MATCHED EXP: 2 REC: 2
# KERNEL: --------------------------
```
