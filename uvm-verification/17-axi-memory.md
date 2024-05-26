# Verification of AXI Memory

## Design Code
```
///////////////////////////////////////////////
module axi_slave(
  ////////////////global control signals
  input clk,
  input resetn,
  
  ///////////////////write address channel
  
  input  awvalid,  /// master is sending new address  
  output reg awready,  /// slave is ready to accept request
  input [3:0] awid, ////// unique ID for each transaction
  input [3:0] awlen, ////// burst length AXI3 : 1 to 16, AXI4 : 1 to 256
  input [2:0] awsize, ////unique transaction size : 1,2,4,8,16 ...128 bytes
  input [31:0] awaddr, ////write adress of transaction
  input [1:0] awburst, ////burst type : fixed , INCR , WRAP
  
  /////////////////////write data channel
  
  input wvalid, //// master is sending new data
  output reg wready, //// slave is ready to accept new data 
  input [3:0] wid, /// unique id for transaction
  input [31:0] wdata, //// data 
  input [3:0] wstrb, //// lane having valid data
  input wlast, //// last transfer in write burst
 
  ///////////////write response channel
  
  input bready, ///master is ready to accept response
  output reg bvalid, //// slave has valid response
  output reg [3:0] bid, ////unique id for transaction
  output reg [1:0] bresp, /// status of write transaction 
  
  ////////////// read address channel
  
   output reg	arready,  //read address ready signal from slave
   input [3:0]	arid,      //read address id
   input [31:0]	araddr,		//read address signal
   input [3:0]	arlen,      //length of the burst
   input [2:0]	arsize,		//number of bytes in a transfer
   input [1:0]	arburst,	//burst type - fixed, incremental, wrapping
   input	arvalid,	//address read valid signal
	
 ///////////////////read data channel
   	output reg [3:0] rid,		//read data id
	output reg [31:0]rdata,     //read data from slave
 	output reg [1:0] rresp,		//read response signal
	output reg rlast,		//read data last signal
	output reg rvalid,		//read data valid signal
	input rready
  
);
  
  
  //axi_if vif();
  typedef enum bit [1:0] {awidle = 2'b00, awstart = 2'b01, awreadys = 2'b10} awstate_type;
  awstate_type awstate, awnext_state;
  
  reg [31:0] awaddrt;
  
  //////reset decoder 
  always_ff@(posedge clk , negedge resetn)
    begin
      if(!resetn) begin
        awstate <= awidle;  ///idle state for write address FSM
        wstate  <= widle;   ///idle state for write data fsm
        bstate  <= bidle;  ///// idle state for write response fsm
        end
      else
        begin
        awstate <= awnext_state;
        wstate  <= wnext_state;
        bstate  <= bnext_state;
        end
    end
  
  
  /////////////fsm for write address channel
  always_comb
    begin
      case(awstate)
      awidle:
      begin
         awready  = 1'b0;
         awnext_state = awstart;  
      end
      
      awstart: 
      begin
        if(awvalid)  
          begin
          awnext_state = awreadys;
          awaddrt      = awaddr;  ////storing address 
          end
        else
          awnext_state = awstart;
      end
      
      awreadys: 
      begin
        
        awready  = 1'b1;
        
        if(wstate == wreadys)
        awnext_state  = awidle;
        else
        awnext_state =  awreadys;
      end  
     endcase
    end
  
  
  
  ////////////////////fsm for write data channel
  
  
  reg [31:0] wdatat;
  reg [7:0] mem[128] = '{default:12};
  reg [31:0] retaddr;
  reg [31:0] nextaddr;
  reg first; /// check operation executed first time
 
 
 
 ///////////////////////////function to compute next address during FIXED burst type 
    function bit[31:0] data_wr_fixed (input [3:0] wstrb, input [31:0] awaddrt);
    unique case (wstrb)
      4'b0001: begin 
        mem[awaddrt] = wdatat[7:0];
      end
      
      4'b0010: begin 
        mem[awaddrt] = wdatat[15:8];
      end
      
      4'b0011: begin 
        mem[awaddrt] = wdatat[7:0];
        mem[awaddrt + 1] = wdatat[15:8];
      end
      
       4'b0100: begin 
         mem[awaddrt] = wdatat[23:16];
      end
      
       4'b0101: begin 
        mem[awaddrt] = wdatat[7:0];
         mem[awaddrt + 1] = wdatat[23:16];
      end
      
      
       4'b0110: begin 
        mem[awaddrt] = wdatat[15:8];
         mem[awaddrt + 1] = wdatat[23:16];
      end
      
       4'b0111: begin 
         mem[awaddrt] = wdatat[7:0];
         mem[awaddrt + 1] = wdatat[15:8];
         mem[awaddrt + 2] = wdatat[23:16];
      end
      
       4'b1000: begin 
         mem[awaddrt] = wdatat[31:24];
      end
      
       4'b1001: begin 
         mem[awaddrt] = wdatat[7:0];
         mem[awaddrt + 1] = wdatat[31:24];
      end
      
      
       4'b1010: begin 
         mem[awaddrt] = wdatat[15:8];
         mem[awaddrt + 1] = wdatat[31:24];
      end
      
      
       4'b1011: begin 
         mem[awaddrt] = wdatat[7:0];
         mem[awaddrt + 1] = wdatat[15:8];
         mem[awaddrt + 2] = wdatat[31:24];
      end
      
      4'b1100: begin 
         mem[awaddrt] = wdatat[23:16];
         mem[awaddrt + 1] = wdatat[31:24];
      end
 
      4'b1101: begin 
        mem[awaddrt] = wdatat[7:0];
        mem[awaddrt + 1] = wdatat[23:16];
        mem[awaddrt + 2] = wdatat[31:24];
      end
 
      4'b1110: begin 
        mem[awaddrt] = wdatat[15:8];
        mem[awaddrt + 1] = wdatat[23:16];
        mem[awaddrt + 2] = wdatat[31:24];
      end
      
      4'b1111: begin
        mem[awaddrt] = wdatat[7:0];
        mem[awaddrt + 1] = wdatat[15:8];
        mem[awaddrt + 2] = wdatat[23:16];
        mem[awaddrt + 3] = wdatat[31:24];       
      end
     endcase
    return awaddrt;
  endfunction  
 
 
 ///////////////////////////function to compute next address during INCR burst type 
  
     function bit[31:0] data_wr_incr (input [3:0] wstrb, input [31:0] awaddrt);
      
   bit [31:0] addr;
   
    unique case (wstrb)
      4'b0001: begin 
        mem[awaddrt] = wdatat[7:0];
        addr = awaddrt + 1;
      end
      
      4'b0010: begin 
        mem[awaddrt] = wdatat[15:8];
        addr = awaddrt + 1;
      end
      
      4'b0011: begin 
        mem[awaddrt] = wdatat[7:0];
        mem[awaddrt + 1] = wdatat[15:8];
        addr = awaddrt + 2;
      end
      
       4'b0100: begin 
         mem[awaddrt] = wdatat[23:16];
         addr = awaddrt + 1;
      end
      
       4'b0101: begin 
        mem[awaddrt] = wdatat[7:0];
         mem[awaddrt + 1] = wdatat[23:16];
         addr = awaddrt + 2;
      end
      
      
       4'b0110: begin 
         mem[awaddrt] = wdatat[15:8];
         mem[awaddrt + 1] = wdatat[23:16];
         addr = awaddrt + 2;
      end
      
       4'b0111: begin 
         mem[awaddrt] = wdatat[7:0];
         mem[awaddrt + 1] = wdatat[15:8];
         mem[awaddrt + 2] = wdatat[23:16];
         addr = awaddrt + 3;
      end
      
       4'b1000: begin 
         mem[awaddrt] = wdatat[31:24];
         addr = awaddrt + 1;
      end
      
       4'b1001: begin 
         mem[awaddrt] = wdatat[7:0];
         mem[awaddrt + 1] = wdatat[31:24];
         addr = awaddrt + 2;
      end
      
      
       4'b1010: begin 
         mem[awaddrt] = wdatat[15:8];
         mem[awaddrt + 1] = wdatat[31:24];
         addr = awaddrt + 2;
      end
      
      
       4'b1011: begin 
         mem[awaddrt] = wdatat[7:0];
         mem[awaddrt + 1] = wdatat[15:8];
         mem[awaddrt + 2] = wdatat[31:24];
         addr = awaddrt + 3;
      end
      
      4'b1100: begin 
         mem[awaddrt] = wdatat[23:16];
         mem[awaddrt + 1] = wdatat[31:24];
         addr = awaddrt + 2;
      end
 
      4'b1101: begin 
        mem[awaddrt] = wdatat[7:0];
        mem[awaddrt + 1] = wdatat[23:16];
        mem[awaddrt + 2] = wdatat[31:24];
        addr = awaddrt + 3;
      end
 
      4'b1110: begin 
        mem[awaddrt] = wdatat[15:8];
        mem[awaddrt + 1] = wdatat[23:16];
        mem[awaddrt + 2] = wdatat[31:24];
        addr = awaddrt + 3;
      end
      
      4'b1111: begin
        mem[awaddrt] = wdatat[7:0];
        mem[awaddrt + 1] = wdatat[15:8];
        mem[awaddrt + 2] = wdatat[23:16];
        mem[awaddrt + 3] = wdatat[31:24]; 
        addr = awaddrt + 4;      
      end
     endcase
    return addr;
  endfunction   
  
  ///////////////////////Function to compute Wrapping boundary
  
  
     function bit [7:0] wrap_boundary (input bit [3:0] awlen,input bit[2:0] awsize);
       bit [7:0] boundary;
      
     unique case(awlen)
       4'b0001: 
       begin
               unique case(awsize)
                       3'b000: begin
                       boundary = 2 * 1; 
                      end
                       3'b001: begin
                       boundary = 2 * 2;																		
                       end	
                       3'b010: begin
                       boundary = 2 * 4;																		
                       end
                endcase
          end
       4'b0011: 
       begin
               unique case(awsize)
                       3'b000: begin
                       boundary = 4 * 1; 
                      end
                       3'b001: begin
                       boundary = 4 * 2;																		
                       end	
                       3'b010: begin
                       boundary = 4 * 4;																		
                       end
                endcase
          end
       
    4'b0111: 
       begin
               unique case(awsize)
                       3'b000: begin
                       boundary = 8 * 1; 
                      end
                       3'b001: begin
                       boundary = 8 * 2;																		
                       end	
                       3'b010: begin
                       boundary = 8 * 4;																		
                       end
                endcase
          end
  
  
         4'b1111: 
       begin
               unique case(awsize)
                       3'b000: begin
                       boundary = 16 * 1; 
                      end
                       3'b001: begin
                       boundary = 16 * 2;																		
                       end	
                       3'b010: begin
                       boundary = 16 * 4;																		
                       end
                endcase
          end
     
     endcase
     
     
     return boundary;
  endfunction
  //////////////////////////////////////////////////////////////
  
     function bit[31:0] data_wr_wrap (input [3:0] wstrb, input [31:0] awaddrt, input [7:0] wboundary);
      
      bit [31:0] addr1, addr2, addr3, addr4;
      bit [31:0] nextaddr, nextaddr2;
   
    unique case (wstrb)
    
    /////////////////////////////////////////////////
      4'b0001: begin 
        mem[awaddrt] = wdatat[7:0];
        
        if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
        else
           addr1 = awaddrt + 1;
           
      return addr1;      
      end
      
      /////////////////////////////////////////////////
      
      4'b0010: begin 
        mem[awaddrt] = wdatat[15:8];
        
       if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
        else
           addr1 = awaddrt + 1;
           
      return addr1;   
      end
      
      ///////////////////////////////////////////////////
      
      4'b0011: begin 
        mem[awaddrt] = wdatat[7:0];
        
       if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
        else
           addr1 = awaddrt + 1;
                  
       mem[addr1] = wdatat[15:8]; 
              
       if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
           
        return addr2;   
           
       end
        
      ///////////////////////////////////////////////  
      
       4'b0100: begin 
         mem[awaddrt] = wdatat[23:16];
         
        if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
        else
           addr1 = awaddrt + 1;
           
       return addr1;
      end
      
      //////////////////////////////////////////////
      
       4'b0101: begin 
        mem[awaddrt] = wdatat[7:0];
        
          if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
        
        
        mem[addr1] = wdatat[23:16];
        
        
          if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
           
        return addr2;  
            
      end
      
      ///////////////////////////////////////////////////
      
       4'b0110: begin 
        mem[awaddrt] = wdatat[15:8];
        
          if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
        
         mem[addr1] = wdatat[23:16];
         
         if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
           
        return addr2;  
        
      end
    //////////////////////////////////////////////////////////////
      
       4'b0111: begin 
         mem[awaddrt] = wdatat[7:0];    
          if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
          
         mem[addr1] = wdatat[15:8];
         
        if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
           
         mem[addr2] = wdatat[23:16];
         
        if((addr2 + 1) % wboundary == 0)
           addr3 = (addr2 + 1) - wboundary;
        else
           addr3 = addr2 + 1;
          
          return addr3;
     end
      
       4'b1000: begin 
         mem[awaddrt] = wdatat[31:24];
         
         if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
           
           return addr1;
      end
      
       4'b1001: begin 
         mem[awaddrt] = wdatat[7:0];
         
         if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
           
           
         mem[addr1] = wdatat[31:24];
         
         if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
         
        return addr2;
      end
      
      
       4'b1010: begin 
         mem[awaddrt] = wdatat[15:8];
         
         if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
         
         mem[addr1] = wdatat[31:24];
         
        if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
         
        return addr2;
      end
      
      
       4'b1011: begin 
         mem[awaddrt] = wdatat[7:0];
         
          if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
         
         
         mem[addr1] = wdatat[15:8];
         
         if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
           
         mem[addr2] = wdatat[31:24];
         
        if((addr2 + 1) % wboundary == 0)
           addr3 = (addr2 + 1) - wboundary;
        else
           addr3 = addr2 + 1;
                     
       return addr3;
       
      end
      
      4'b1100: begin 
         mem[awaddrt] = wdatat[23:16];
         
           if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
         
         mem[addr1] = wdatat[31:24];
         
         if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
           
           return addr2;
      end
 
      4'b1101: begin 
        mem[awaddrt] = wdatat[7:0];
        
           if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
        
        mem[addr1] = wdatat[23:16];
        
         if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
        
        mem[addr2] = wdatat[31:24];
        
         if((addr2 + 1) % wboundary == 0)
           addr3 = (addr2 + 1) - wboundary;
        else
           addr3 = addr2 + 1;
                     
       return addr3;
        
      end
 
      4'b1110: begin 
        mem[awaddrt] = wdatat[15:8];
        
         if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
        
        mem[addr1] = wdatat[23:16];
        
         if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
        
        mem[addr2] = wdatat[31:24];
        
        if((addr2 + 1) % wboundary == 0)
           addr3 = (addr2 + 1) - wboundary;
        else
           addr3 = addr2 + 1;
           
           return addr3;
      end
      
      4'b1111: begin
        mem[awaddrt] = wdatat[7:0];
           
           if((awaddrt + 1) % wboundary == 0)
           addr1 = (awaddrt + 1) - wboundary;
          else
           addr1 = awaddrt + 1;
        
        mem[addr1] = wdatat[15:8];
        
         if((addr1 + 1) % wboundary == 0)
           addr2 = (addr1 + 1) - wboundary;
        else
           addr2 = addr1 + 1;
        
        mem[addr2] = wdatat[23:16];
        
         if((addr2 + 1) % wboundary == 0)
           addr3 = (addr2 + 1) - wboundary;
        else
           addr3 = addr2 + 1;
        
        
        mem[addr3] = wdatat[31:24]; 
        
       if((addr3 + 1) % wboundary == 0)
           addr4 = (addr3 + 1) - wboundary;
        else
           addr4 = addr3 + 1;
           
         return addr4;        
      end
     endcase
 
  endfunction   
  
  
  
  
  
  
  
  
  
  reg [7:0] boundary;  ////storing boundary
  reg [3:0] wlen_count;
  
  typedef enum bit [2:0] {widle = 0, wstart = 1, wreadys = 2, wvalids = 3, waddr_dec = 4} wstate_type;
  wstate_type wstate, wnext_state;
  
  always_comb
    begin
      case(wstate)
      
      widle: begin
        wready = 1'b0;
        wnext_state = wstart; 
        first = 1'b0; 
        wlen_count = 0;
      end
      
      wstart: begin
        if(wvalid)
          begin
            wnext_state = waddr_dec;
            wdatat      = wdata;
          end
        else
          begin
            wnext_state = wstart;
          end 
      end
      
      waddr_dec: begin
             wnext_state = wreadys;
             
    
             if(first == 0) begin
               nextaddr  = awaddr;
               first = 1'b1;
               wlen_count = 0;
               end
              else if (wlen_count < (awlen + 1 ))
               begin
               nextaddr = retaddr;      
               end   
              else
                begin
               nextaddr  = awaddr;
                end
      end
      
      
      
      wreadys: begin
         
          if(wlast == 1'b1) begin
           wnext_state = widle;
           wready = 1'b0;
           wlen_count = 0;
           first = 0; 
           end
          else if(wlen_count < (awlen + 1)) 
          begin
           wnext_state = wvalids;
           wready      = 1'b1;
          end
          else
           wnext_state = wreadys;  
          
          
        case(awburst)
          2'b00:  ////Fixed Mode
          begin       
          retaddr = data_wr_fixed(wstrb, awaddr);  ///fixed
          end
          
          2'b01:  ////Incr mode
          begin           
          retaddr =  data_wr_incr(wstrb,nextaddr); 
          end
                                                      
          2'b10:  //// wrapping
          begin
               boundary = wrap_boundary(awlen, awsize);   /////calculate wrapping boundary
               retaddr = data_wr_wrap(wstrb, nextaddr, boundary); ///////generate next addr
            end     
        endcase    
      end
          
          
       wvalids: begin    
       wready      = 1'b0;
       wnext_state = wstart;
       
       if(wlen_count < (awlen + 1))
       wlen_count = wlen_count + 1;
       else
       wlen_count = wlen_count;
         
      end
      endcase    
 end
 
 
 
 ////////////////////////fsm for write response
 
 typedef enum bit [1:0] {bidle = 0, bdetect_last = 1, bstart = 2, bwait = 3} bstate_type;
 bstate_type bstate,bnext_state;
 
 
 always_comb
 begin
   case(bstate)
     bidle: begin 
         bid = 1'b0;
         bresp = 1'b0; 
         bvalid = 1'b0;
         bnext_state = bdetect_last; 
     end
     
     bdetect_last: begin
         if(wlast)
          bnext_state = bstart;
          else
          bnext_state = bdetect_last; 
     end
     
     bstart: begin
      bid = awid;
      bvalid = 1'b1;
      bnext_state = bwait;
       if( (awaddr < 128 ) && (awsize <= 3'b010) )
         bresp = 2'b00;  ///okay
       else if (awsize > 3'b010)
         bresp = 2'b10; /////slverr
       else
          bresp = 2'b11;  ///no slave address   
     end
   
   bwait: begin
      if(bready == 1'b1)
         bnext_state = bidle;
     else
         bnext_state = bwait;
   end
   
   endcase
 end 
 
 ////////////////////////fsm for read address
 
 always_ff @(posedge clk, negedge resetn)
 begin
    if(!resetn)
       begin
       arstate <= aridle;
       rstate  <= ridle;
       end
       else
       begin
       arstate <= arnext_state;
       rstate  <= rnext_state;
       end
 end
 
 
 typedef enum bit [1:0] {aridle = 0, arstart = 1, arreadys = 2} arstate_type;
 arstate_type arstate, arnext_state;
 
 reg [31:0] araddrt; ///register address
 
 always_comb
 begin 
 case(arstate)
   aridle: begin
      arready = 1'b0;
      arnext_state = arstart;
   end
   
   arstart: begin
      if(arvalid == 1'b1) begin
         arnext_state = arreadys;
         araddrt = araddr; 
         end
       else
         arnext_state = arstart;   
   end
   
   arreadys: begin
          arnext_state = aridle;
          arready = 1'b1;
   end
 endcase
 end
 
 ///////////////////////////read data in FIxed Mode
 
    function void read_data_fixed (input [31:0] addr, input [2:0] arsize);
                 unique case(arsize)
                 3'b000: begin
                  rdata[7:0] = mem[addr];    
                 end
                  
                 3'b001: begin
                  rdata[7:0]  = mem[addr]; 
                  rdata[15:8] = mem[addr + 1]; 
                 end 
                 
                 3'b010: begin
                  rdata[7:0]    = mem[addr]; 
                  rdata[15:8]   = mem[addr + 1]; 
                  rdata[23:16]  = mem[addr + 2]; 
                  rdata[31:24]  = mem[addr + 3]; 
                 end
                 endcase       
   endfunction
 //////////////////////////end of function
 //////////////////////////// read data in INCR Mode
   
     function bit [31:0] read_data_incr (input [31:0] addr, input [2:0] arsize);
      bit [31:0] nextaddr;
      
      unique case(arsize)
        3'b000: begin
          rdata[7:0] = mem[addr];
          nextaddr = addr + 1;
       end
       
       3'b001: begin
       rdata[7:0]  = mem[addr];
       rdata[15:8] = mem[addr + 1];
       nextaddr = addr + 2;  
       end
       
       3'b010: begin
       rdata[7:0]    = mem[addr];
       rdata[15:8]   = mem[addr + 1];
       rdata[23:16]  = mem[addr + 2];
       rdata[31:24]  = mem[addr + 3];
       nextaddr = addr + 4;  
       end
      
      endcase
      
      return nextaddr;
      
     endfunction
 
 ///////////////////////////////////////////end of function 
  function bit [31:0] read_data_wrap (input bit [31:0] addr, input bit [2:0] rsize, input [7:0] rboundary);
    bit [31:0] addr1,addr2,addr3,addr4;
    
    unique case (rsize)
     3'b000: begin
        rdata[7:0] = mem[addr];
        
        if(((addr + 1) % rboundary ) == 0)
               addr1 = (addr + 1) - rboundary;
        else
               addr1 = (addr + 1);
               
        return addr1;       
     end
     
     3'b001: begin
        rdata[7:0] = mem[addr];
        
         if(((addr + 1) % rboundary ) == 0)
               addr1 = (addr + 1) - rboundary;
        else
               addr1 = (addr + 1);
               
         rdata[15:8] = mem[addr1];
         
         if(((addr1 + 1) % rboundary ) == 0)
               addr2 = (addr1 + 1) - rboundary;
        else
               addr2 = (addr1 + 1);         
               
        return addr2;       
     end
     
     3'b010:  begin
     
         rdata[7:0] = mem[addr];
        
         if(((addr + 1) % rboundary ) == 0)
               addr1 = (addr + 1) - rboundary;
        else
               addr1 = (addr + 1);
               
         rdata[15:8] = mem[addr1];
         
         if(((addr1 + 1) % rboundary ) == 0)
               addr2 = (addr1 + 1) - rboundary;
        else
               addr2 = (addr1 + 1);  
               
         rdata[23:16]  = mem[addr2];
           
        if(((addr2 + 1) % rboundary ) == 0)
               addr3 = (addr2 + 1) - rboundary;
        else
               addr3 = (addr2 + 1); 
          
          rdata[31:24] = mem[addr3];
          
         if(((addr3 + 1) % rboundary ) == 0)
               addr4 = (addr3 + 1) - rboundary;
        else
               addr4 = (addr3 + 1);            
     
       return addr4;
     end
     
   endcase
  
  endfunction
 
/////////////////////////////////////// 
 reg rdfirst;
 bit [31:0] rdnextaddr, rdretaddr;
 reg [3:0] len_count;
 reg [7:0] rdboundary;
 
 typedef enum bit [2:0] {ridle = 0, rstart = 1, rwait = 2, rvalids = 3, rerror = 4} rstate_type;
 rstate_type rstate, rnext_state;
 
 /////////////////////////////////
 always_comb
 begin
 case(rstate)
     ridle: begin
     
     rid = 0;
     rdfirst = 0;
     rdata = 0;
     rresp = 0;
     rlast = 0;
     rvalid = 0;
     len_count = 0;
     
     if(arvalid)
     rnext_state = rstart;
     else
     rnext_state = ridle; 
    end
    
    rstart: begin
      if ((araddrt < 128) && (arsize <= 3'b010) ) begin
        rid = arid;
        rvalid = 1'b1;
        rnext_state = rwait;
        rresp = 2'b00;   
        unique case(arburst)
        
         ////////////////////fixed
          2'b00: begin
              if(rdfirst == 0) begin
               rdnextaddr  = araddr;
               rdfirst = 1'b1;
               len_count = 0;
               end
             else if (len_count != (arlen + 1))
               begin
               rdnextaddr  = araddr;
               end
      
              read_data_fixed(araddrt, arsize);
            end
      //////////////////////end of fixed
      
      ////////////////////start of incr
      2'b01: begin
              if(rdfirst == 0) begin
               rdnextaddr  = araddr;
               rdfirst = 1'b1;
               len_count = 0;
               end
             else if (len_count != (arlen + 1))
               begin
               rdnextaddr = rdretaddr;
               end   
                               
             rdretaddr = read_data_incr(rdnextaddr, arsize); 
             end    
    ///////////////////////end of incr      
    2'b10: begin
               if(rdfirst == 0) 
               begin
               rdnextaddr  = araddr;
               rdfirst = 1'b1;
               len_count = 0;
               end
             else if (len_count != (arlen + 1))
               begin
               rdnextaddr = rdretaddr;    
               end    
        rdboundary = wrap_boundary(arlen, arsize);
        rdretaddr  = read_data_wrap(rdnextaddr, arsize, rdboundary);
        end
   endcase
      end
      else if ( (araddr >= 128) && ( arsize <= 3'b010) ) begin 
        rresp = 2'b11;  
        rvalid = 1'b1;
        rnext_state = rerror; 
      end
      else if (arsize > 3'b010) begin
        rresp = 2'b10;
        rvalid = 1'b1;
        rnext_state = rerror;
       end  
   
  end
  
   rwait: begin
      rvalid = 1'b0;
      if(rready == 1'b1)
           rnext_state = rvalids; 
         else
         rnext_state = rwait;
   end
   
   rvalids: begin
       len_count = len_count + 1;
       if(len_count == (arlen + 1))
       begin
        rnext_state = ridle;
        rlast       = 1'b1;
       end
       else
         begin
        rnext_state = rstart;
        rlast       = 1'b0;
         end 
   end
   
   rerror : begin 
       rvalid = 1'b0;
     
         if(len_count < (arlen)) 
            begin
            if(arready) 
              begin
              rnext_state = rstart;
              len_count = len_count + 1;
              end
            end
         else
            begin
            rlast = 1'b1; 
            rnext_state = ridle;
            len_count   = 0;
            end 
        end 
        
        
   default : rnext_state = ridle;
 endcase  
 end
endmodule
 
 
//////////////////////////////////////////////
 
interface axi_if();
  
  ////////write address channel (aw)
  
  logic awvalid;  /// master is sending new address  
  logic awready;  /// slave is ready to accept request
  logic [3:0] awid; ////// unique ID for each transaction
  logic [3:0] awlen; ////// burst length AXI3 : 1 to 16, AXI4 : 1 to 256
  logic [2:0] awsize; ////unique transaction size : 1,2,4,8,16 ...128 bytes
  logic [31:0] awaddr; ////write adress of transaction
  logic [1:0] awburst; ////burst type : fixed , INCR , WRAP
  
  
  //////////write data channel (w)
  logic wvalid; //// master is sending new data
  logic wready; //// slave is ready to accept new data 
  logic [3:0] wid; /// unique id for transaction
  logic [31:0] wdata; //// data 
  logic [3:0] wstrb; //// lane having valid data
  logic wlast; //// last transfer in write burst
  
  
  //////////write response channel (b) 
  logic bready; ///master is ready to accept response
  logic bvalid; //// slave has valid response
  logic [3:0] bid; ////unique id for transaction
  logic [1:0] bresp; /// status of write transaction 
  
  ///////////////read address channel (ar)
 
  logic arvalid;  /// master is sending new address  
  logic arready;  /// slave is ready to accept request
  logic [3:0] arid; ////// unique ID for each transaction
  logic [3:0] arlen; ////// burst length AXI3 : 1 to 16, AXI4 : 1 to 256
  logic [2:0] arsize; ////unique transaction size : 1,2,4,8,16 ...128 bytes
  logic [31:0] araddr; ////write adress of transaction
  logic [1:0] arburst; ////burst type : fixed , INCR , WRAP
  
  /////////// read data channel (r)
  
  logic rvalid; //// master is sending new data
  logic rready; //// slave is ready to accept new data 
  logic [3:0] rid; /// unique id for transaction
  logic [31:0] rdata; //// data 
  logic [3:0] rstrb; //// lane having valid data
  logic rlast; //// last transfer in write burst
  logic [1:0] rresp; ///status of read transfer
  
  ////////////////
  
  logic clk;
  logic resetn;
  
  //////////////////
  logic [31:0] next_addrwr;
  logic [31:0] next_addrrd;
  
  
 
  
endinterface 
```
## Verification
```
`include "uvm_macros.svh"
 import uvm_pkg::*;
 
 
typedef enum bit [2:0] {wrrdfixed = 0, wrrdincr = 1, wrrdwrap = 2, wrrderrfix = 3,   rstdut = 4 } oper_mode;
 
class transaction extends uvm_sequence_item;
  `uvm_object_utils(transaction)
  
   
 
  function new(string name = "transaction");
    super.new(name);
  endfunction
  
 
  int len = 0;
  rand bit [3:0] id;
  oper_mode op;
  rand bit awvalid;
  bit awready;
  bit [3:0] awid;
  rand bit [3:0] awlen;
  rand bit [2:0] awsize; //4byte =010
  rand bit [31:0] awaddr;
  rand bit [1:0] awburst;
  
  bit wvalid;
  bit wready;
  bit [3:0] wid;
  rand bit [31:0] wdata;
  rand bit [3:0] wstrb;
  bit wlast;
  
  bit bready;
  bit bvalid;
  bit [3:0] bid;
  bit [1:0] bresp;
  
  
  rand bit arvalid;  /// master is sending new address  
  bit arready;  /// slave is ready to accept request
  bit [3:0] arid; ////// unique ID for each transaction
  rand bit [3:0] arlen; ////// burst length AXI3 : 1 to 16, AXI4 : 1 to 256
  bit [2:0] arsize; ////unique transaction size : 1,2,4,8,16 ...128 bytes
  rand bit [31:0] araddr; ////write adress of transaction
  rand bit [1:0] arburst; ////burst type : fixed , INCR , WRAP
  
  /////////// read data channel (r)
  
  bit rvalid; //// master is sending new data
  bit rready; //// slave is ready to accept new data 
  bit [3:0] rid; /// unique id for transaction
  bit [31:0] rdata; //// data 
  bit [3:0] rstrb; //// lane having valid data
  bit rlast; //// last transfer in write burst
  bit [1:0] rresp; ///status of read transfer
  
  //constraint size { awsize == 3'b010; arsize == 3'b010;}
  constraint txid { awid == id; wid == id; bid == id; arid == id; rid == id;  }
  constraint burst {awburst inside {0,1,2}; arburst inside {0,1,2};}
  constraint valid {awvalid != arvalid;}
  constraint length {awlen == arlen;}
 
endclass : transaction
 
 
 
////////////////////////////////////////////////////////////////////////////////
 
class rst_dut extends uvm_sequence#(transaction);
  `uvm_object_utils(rst_dut)
  
  transaction tr;
 
  function new(string name = "rst_dut");
    super.new(name);
  endfunction
 
  
  virtual task body();
    repeat(5)
      begin
        tr = transaction::type_id::create("tr");
         $display("------------------------------");
        `uvm_info("SEQ", "Sending RST Transaction to DRV", UVM_NONE);
        start_item(tr);
        assert(tr.randomize);
        tr.op      = rstdut;
        finish_item(tr);
      end
  endtask
  
 
endclass
 
 
 
 
///////////////////////////////////////////////////////////////////////
 
class valid_wrrd_fixed extends uvm_sequence#(transaction);
  `uvm_object_utils(valid_wrrd_fixed)
  
  transaction tr;
 
  function new(string name = "valid_wrrd_fixed");
    super.new(name);
  endfunction
 
  
  virtual task body();
 
        tr = transaction::type_id::create("tr");
        $display("------------------------------");
        `uvm_info("SEQ", "Sending Fixed mode Transaction to DRV", UVM_NONE);
        start_item(tr);
        assert(tr.randomize);
          tr.op      = wrrdfixed;
          tr.awlen   = 7;
          tr.awburst = 0;
          tr.awsize  = 2;
       
        finish_item(tr);
  endtask
  
 
endclass
////////////////////////////////////////////////////////////
 
class valid_wrrd_incr extends uvm_sequence#(transaction);
  `uvm_object_utils(valid_wrrd_incr)
  
  transaction tr;
 
  function new(string name = "valid_wrrd_incr");
    super.new(name);
  endfunction
 
  
  virtual task body();
        tr = transaction::type_id::create("tr");
        $display("------------------------------");
        `uvm_info("SEQ", "Sending INCR mode Transaction to DRV", UVM_NONE);
        start_item(tr);
        assert(tr.randomize);
          tr.op      = wrrdincr;
          tr.awlen   = 7;
          tr.awburst = 1;
          tr.awsize  = 2;
          
        finish_item(tr);
  endtask
  
 
endclass
 
///////////////////////////////////////////////////////////
 
class valid_wrrd_wrap extends uvm_sequence#(transaction);
  `uvm_object_utils(valid_wrrd_wrap)
  
  transaction tr;
 
  function new(string name = "valid_wrrd_wrap");
    super.new(name);
  endfunction
 
  
  virtual task body();
        tr = transaction::type_id::create("tr");
         $display("------------------------------");
        `uvm_info("SEQ", "Sending WRAP mode Transaction to DRV", UVM_NONE);
        start_item(tr);
        assert(tr.randomize);
          tr.op      = wrrdwrap;
          tr.awlen   = 7;
          tr.awburst = 2;
          tr.awsize  = 2;
          
        finish_item(tr);
  endtask
  
 
endclass
 
/////////////////////////////////////////////////////////////////////////////////
 
class err_wrrd_fix extends uvm_sequence#(transaction);
  `uvm_object_utils(err_wrrd_fix)
  
  transaction tr;
 
  function new(string name = "err_wrrd_fix");
    super.new(name);
  endfunction
 
  
  virtual task body();
        tr = transaction::type_id::create("tr");
        $display("------------------------------");
        `uvm_info("SEQ", "Sending Error Transaction to DRV", UVM_NONE);
        start_item(tr);
        assert(tr.randomize);
          tr.op      = wrrderrfix;
          tr.awlen   = 7;
          tr.awburst = 0;
          tr.awsize  = 2;   
        finish_item(tr);
  endtask
  
 
endclass
 
 
 
 
 
 
 
 
/////////////////////////////////////////////////////////////
class driver extends uvm_driver #(transaction);
  `uvm_component_utils(driver)
  
  virtual axi_if vif;
  transaction tr;
  
  
  function new(input string path = "drv", uvm_component parent = null);
    super.new(path,parent);
  endfunction
  
 virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
     tr = transaction::type_id::create("tr");
      
   if(!uvm_config_db#(virtual axi_if)::get(this,"","vif",vif)) 
      `uvm_error("drv","Unable to access Interface");
  endfunction
  
  
  
  task reset_dut(); 
    begin
    `uvm_info("DRV", "System Reset : Start of Simulation", UVM_MEDIUM);
    vif.resetn      <= 1'b0;  ///active high reset
    vif.awvalid     <= 1'b0;
    vif.awid        <= 1'b0;
    vif.awlen       <= 0;
    vif.awsize      <= 0;
    vif.awaddr      <= 0;
    vif.awburst     <= 0;
      
    vif.wvalid      <= 0;
    vif.wid         <= 0;
    vif.wdata       <= 0;
    vif.wstrb       <= 0;
    vif.wlast       <= 0;
      
    vif.bready      <= 0;
    
    vif.arvalid     <= 1'b0;
    vif.arid        <= 1'b0;
    vif.arlen       <= 0;
    vif.arsize      <= 0;
    vif.araddr      <= 0;
    vif.arburst     <= 0; 
      
    vif.rready      <= 0;
     @(posedge vif.clk);
      end
  endtask
  
  
  /////////////////////////write read in fixed mode
  
  task wrrd_fixed_wr();
            `uvm_info("DRV", "Fixed Mode Write Transaction Started", UVM_NONE);
    /////////////////////////write logic
            vif.resetn      <= 1'b1;
            vif.awvalid     <= 1'b1;
            vif.awid        <= tr.id;
            vif.awlen       <= 7;
            vif.awsize      <= 2;
            vif.awaddr      <= 5;
            vif.awburst     <= 0;
     
     
            vif.wvalid      <= 1'b1;
            vif.wid         <= tr.id;
            vif.wdata       <= $urandom_range(0,10);
            vif.wstrb       <= 4'b1111;
            vif.wlast       <= 0;
     
            vif.arvalid     <= 1'b0;  ///turn off read 
            vif.rready      <= 1'b0;
            vif.bready      <= 1'b0;
             @(posedge vif.clk);
            
             @(posedge vif.wready);
             @(posedge vif.clk);
 
     for(int i = 0; i < (vif.awlen); i++)//0 - 6 -> 7
         begin
            vif.wdata       <= $urandom_range(0,10);
            vif.wstrb       <= 4'b1111;
            @(posedge vif.wready);
            @(posedge vif.clk);
         end
         vif.awvalid     <= 1'b0;
         vif.wvalid      <= 1'b0;
         vif.wlast       <= 1'b1;
         vif.bready      <= 1'b1;
         @(negedge vif.bvalid); 
         vif.wlast       <= 1'b0;
         vif.bready      <= 1'b0;  
        /////////////////////////////////////// read logic
   endtask
   
   ///////////////////////////////////////////////////////// read transaction in fixed mode
   
        task  wrrd_fixed_rd(); 
        `uvm_info("DRV", "Fixed Mode Read Transaction Started", UVM_NONE);   
        @(posedge vif.clk);
 
        vif.arid        <= tr.id;
        vif.arlen       <= 7;
        vif.arsize      <= 2;
        vif.araddr      <= 5;
        vif.arburst     <= 0; 
        vif.arvalid     <= 1'b1;  
        vif.rready      <= 1'b1;
       
        
     for(int i = 0; i < (vif.arlen + 1); i++) begin // 0 1  2 3 4 5 6 7
       @(posedge vif.arready);
       @(posedge vif.clk);
      end
      
     @(negedge vif.rlast);      
     vif.arvalid <= 1'b0;
     vif.rready  <= 1'b0; 
 
  endtask
  
 ////////////////////////////////////////////////////////////////////// 
 
  
   task wrrd_incr_wr();
   /////////////////////////write logic
    `uvm_info("DRV", "INCR Mode Write Transaction Started", UVM_NONE);
            vif.resetn      <= 1'b1;
            vif.awvalid     <= 1'b1;
            vif.awid        <= tr.id;
            vif.awlen       <= 7;
            vif.awsize      <= 2;
            vif.awaddr      <= 5;
            vif.awburst     <= 1;
     
     
            vif.wvalid      <= 1'b1;
            vif.wid         <= tr.id;
            vif.wdata       <= $urandom_range(0,10);
            vif.wstrb       <= 4'b1111;
            vif.wlast       <= 0;
     
            vif.arvalid     <= 1'b0;  ///turn off read 
            vif.rready      <= 1'b0;
            vif.bready      <= 1'b0;
            
            
             @(posedge vif.wready);
             @(posedge vif.clk);
 
     for(int i = 0; i < (vif.awlen); i++)
         begin
            vif.wdata       <= $urandom_range(0,10);
            vif.wstrb       <= 4'b1111;
            @(posedge vif.wready);
            @(posedge vif.clk);
         end
     
         vif.wlast       <= 1'b1;
         vif.bready      <= 1'b1;
         vif.awvalid     <= 1'b0;
         vif.wvalid      <= 1'b0;
         @(negedge vif.bvalid);
         vif.bready      <= 1'b0;
          vif.wlast      <= 1'b0; 
           
      endtask   
      
        /////////////////////////////////////// read logic
     task wrrd_incr_rd();  
       `uvm_info("DRV", "INCR Mode Read Transaction Started", UVM_NONE);  
       @(posedge vif.clk);
 
       
 
        vif.arid        <= tr.id;
        vif.arlen       <= 7;
        vif.arsize      <= 2;
        vif.araddr      <= 5;
        vif.arburst     <= 1; 
        vif.arvalid     <= 1'b1;  
        vif.rready      <= 1'b1;
        
     for(int i = 0; i < (vif.arlen + 1); i++) begin // 0 1  2 3 4 5 6 7
       @(posedge vif.arready);
       @(posedge vif.clk);
      end
      
     @(negedge vif.rlast);
     vif.arvalid <= 1'b0;
     vif.rready  <= 1'b0; 
  endtask
 
//////////////////////////////////////////////////////////////////////////////
 
   task wrrd_wrap_wr();
    `uvm_info("DRV", "WRAP Mode Write Transaction Started", UVM_NONE);  
   /////////////////////////write logic
            vif.resetn      <= 1'b1;
            vif.awvalid     <= 1'b1;
            vif.awid        <= tr.id;
            vif.awlen       <= 7;
            vif.awsize      <= 2;
            vif.awaddr      <= 5;
            vif.awburst     <= 2;
     
     
            vif.wvalid      <= 1'b1;
            vif.wid         <= tr.id;
            vif.wdata       <= $urandom_range(0,10);
            vif.wstrb       <= 4'b1111;
            vif.wlast       <= 0;
     
            vif.arvalid     <= 1'b0;  ///turn off read 
            vif.rready      <= 1'b0;
            vif.bready      <= 1'b0;
            
            
             @(posedge vif.wready);
             @(posedge vif.clk);
 
       for(int i = 0; i < (vif.awlen); i++)
         begin
            vif.wdata       <= $urandom_range(0,10);
            vif.wstrb       <= 4'b1111;
            @(posedge vif.wready);
            @(posedge vif.clk);
         end
     
         vif.wlast       <= 1'b1;
         vif.bready      <= 1'b1;
         vif.awvalid     <= 1'b0;
         vif.wvalid      <= 1'b0;
        
         @(negedge vif.bvalid);
         vif.bready      <= 1'b0; 
         vif.wlast       <= 1'b0; 
         
         
        endtask 
         
         
         
        /////////////////////////////////////// read logic
       task wrrd_wrap_rd(); 
      `uvm_info("DRV", "WRAP Mode Read Transaction Started", UVM_NONE);  
       @(posedge vif.clk);
       vif.arvalid     <= 1'b1;  
       vif.rready      <= 1'b1;
  
 
        vif.arid        <= tr.id;
        vif.arlen       <= 7;
        vif.arsize      <= 2;
        vif.araddr      <= 5;
        vif.arburst     <= 2; 
        
     for(int i = 0; i < (vif.arlen + 1); i++) begin // 0 1  2 3 4 5 6 7
       @(posedge vif.arready);
       @(posedge vif.clk);
      end
     
     @(negedge vif.rlast);
     vif.arvalid <= 1'b0; 
     vif.rready  <= 1'b0; 
  endtask
  
  //////////////////////////////////////////////////////////////////////////
  
      task err_wr();
      `uvm_info("DRV", "Error Write Transaction Started", UVM_NONE);
   
   /////////////////////////write logic
            vif.resetn      <= 1'b1;
            vif.awvalid     <= 1'b1;
            vif.awid        <= tr.id;
            vif.awlen       <= 7;
            vif.awsize      <= 2;
            vif.awaddr      <= 128;
            vif.awburst     <= 0;
     
     
            vif.wvalid      <= 1'b1;
            vif.wid         <= tr.id;
            vif.wdata       <= $urandom_range(0,10);
            vif.wstrb       <= 4'b1111;
            vif.wlast       <= 0;
     
            vif.arvalid     <= 1'b0;  ///turn off read 
            vif.rready      <= 1'b0;
            vif.bready      <= 1'b0;
            
            
             @(posedge vif.wready);
             @(posedge vif.clk);
 
     for(int i = 0; i < (vif.awlen); i++)
         begin
            vif.wdata       <= $urandom_range(0,10);
            vif.wstrb       <= 4'b1111;
            @(posedge vif.wready);
            @(posedge vif.clk);
         end
     
         vif.wlast       <= 1'b1;
         vif.bready      <= 1'b1;
         vif.awvalid     <= 1'b0;
         vif.wvalid      <= 1'b0;
         
         @(negedge vif.bvalid);
         vif.bready      <= 1'b0;
         vif.wlast       <= 1'b0;
        endtask
        
           
        /////////////////////////////////////// read logic
       task err_rd();  
        `uvm_info("DRV", "Error Read Transaction Started", UVM_NONE);
       @(posedge vif.clk);
       vif.arvalid     <= 1'b1;  
       vif.rready      <= 1'b1;
       //vif.bready      <= 1'b1;
 
        vif.arid        <= tr.id;
        vif.arlen       <= 7;
        vif.arsize      <= 2;
        vif.araddr      <= 128;
        vif.arburst     <= 0; 
        
     for(int i = 0; i < (vif.arlen + 1); i++) begin // 0 1  2 3 4 5 6 7
       @(posedge vif.arready);
       @(posedge vif.clk);
      end
     
     @(negedge vif.rlast);
     vif.arvalid <= 1'b0; 
     vif.rready  <= 1'b0; 
  
    endtask
  ////////////////////////////////////////////////////////////////////////
 
 
  virtual task run_phase(uvm_phase phase);
       forever begin
     
         seq_item_port.get_next_item(tr);
            if(tr.op == rstdut)
             reset_dut();
           else if (tr.op == wrrdfixed)
             begin
            `uvm_info("DRV", $sformatf("Fixed Mode Write -> Read WLEN:%0d WSIZE:%0d",tr.awlen+1,tr.awsize), UVM_MEDIUM);
             wrrd_fixed_wr();
             wrrd_fixed_rd();
             end
           else if (tr.op == wrrdincr)
             begin
            `uvm_info("DRV", $sformatf("INCR Mode Write -> Read WLEN:%0d WSIZE:%0d",tr.awlen+1,tr.awsize), UVM_MEDIUM);
             wrrd_incr_wr();
             wrrd_incr_rd();
             end   
           else if (tr.op == wrrdwrap)
             begin
            `uvm_info("DRV", $sformatf("WRAP Mode Write -> Read WLEN:%0d WSIZE:%0d",tr.awlen+1,tr.awsize), UVM_MEDIUM);
             wrrd_wrap_wr();
             wrrd_wrap_rd();
             end   
           else if (tr.op == wrrderrfix)
             begin
            `uvm_info("DRV", $sformatf("Error Transaction Mode WLEN:%0d WSIZE:%0d",tr.awlen+1,tr.awsize), UVM_MEDIUM);
             err_wr();
             err_rd();
             end 
 
         seq_item_port.item_done();
        end
  endtask
 
  
endclass
///////////////////////////////////////////////////////////////////////
 
 
 
class mon extends uvm_monitor;
`uvm_component_utils(mon)
 
transaction tr;
virtual axi_if vif;
  
  logic [31:0] arr[128];
    
  logic [1:0] rdresp;
  logic [1:0] wrresp;
  
  logic       resp;
  
  int err = 0;
 
    function new(input string inst = "mon", uvm_component parent = null);
    super.new(inst,parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tr = transaction::type_id::create("tr");
      if(!uvm_config_db#(virtual axi_if)::get(this,"","vif",vif))//uvm_test_top.env.agent.drv.aif
        `uvm_error("MON","Unable to access Interface");
    endfunction
  
  
  /////////////////////////////////////////////////////////////////////////
  
  task compare();
    if(err == 0 && rdresp == 0 && wrresp == 0 )
         begin
           `uvm_info("MON", $sformatf("Test Passed err :%0d wrresp :%0d rdresp :%0d ", err, rdresp, wrresp), UVM_MEDIUM); 
           err = 0;
         end
    else
        begin
          `uvm_info("MON", $sformatf("Test Failed err :%0d wrresp :%0d rdresp :%0d ", err, rdresp, wrresp), UVM_MEDIUM);
          err = 0; 
        end
  endtask
  
    
  ///////////////////////////////////////////////////////////////////////  
    virtual task run_phase(uvm_phase phase);
    forever begin
    
      @(posedge vif.clk);
      if(!vif.resetn)
        begin 
          `uvm_info("MON", "System Reset Detected", UVM_MEDIUM); 
        end
      
      else if(vif.resetn && vif.awaddr < 128)
        begin
       
          wait(vif.awvalid == 1'b1);
          
          for(int i =0; i < (vif.awlen + 1); i++) begin
          @(posedge vif.wready);
          arr[vif.next_addrwr] = vif.wdata;
          end
          
         // @(negedge vif.wlast);
          @(posedge vif.bvalid);
          wrresp = vif.bresp;///0
  //////////////////////////////////////////////////////        
          wait(vif.arvalid == 1'b1);
          
          for(int i =0; i < (vif.arlen + 1); i++) begin
            @(posedge vif.rvalid);
            if(vif.rdata != arr[vif.next_addrrd])
               begin
               err++;
               end
          end
          
          @(posedge vif.rlast);
          rdresp = vif.rresp;
          
          compare();
           $display("------------------------------");
          end
          
          else if (vif.resetn && vif.awaddr >= 128)
          begin
          wait(vif.awvalid == 1'b1);
          
          for(int i =0; i < (vif.awlen + 1); i++) begin
          @(negedge vif.wready);
          end
          
          @(posedge vif.bvalid);
          wrresp = vif.bresp;
          
          wait(vif.arvalid == 1'b1);
          
          for(int i =0; i < (vif.arlen + 1); i++) begin
            @(posedge vif.arready);
            if(vif.rresp != 2'b00)
               begin
               err++;
               end
          end
          
          @(posedge vif.rlast);
           rdresp = vif.rresp;  
              
              compare();   
           $display("------------------------------");   
         end
      
 end      
endtask 
 
endclass
 
 
 
 
 
 
 
 
 
 
///////////////////////////////////////////////////////////
class agent extends uvm_agent;
`uvm_component_utils(agent)
  
 
 
function new(input string inst = "agent", uvm_component parent = null);
super.new(inst,parent);
endfunction
 
 driver d;
 uvm_sequencer#(transaction) seqr;
 mon m;
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   m = mon::type_id::create("m",this); 
   d = driver::type_id::create("d",this);
   seqr = uvm_sequencer#(transaction)::type_id::create("seqr", this);
  
  
endfunction
 
virtual function void connect_phase(uvm_phase phase);
super.connect_phase(phase);
    d.seq_item_port.connect(seqr.seq_item_export);
endfunction
 
endclass
 
////////////////////////////////////////////////////////////////////////////////
 
class env extends uvm_env;
`uvm_component_utils(env)
 
function new(input string inst = "env", uvm_component c);
super.new(inst,c);
endfunction
 
agent a;
 
 
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
  a = agent::type_id::create("a",this);
 
endfunction
 
 
endclass
 
//////////////////////////////////////////////////
class test extends uvm_test;
`uvm_component_utils(test)
 
function new(input string inst = "test", uvm_component c);
super.new(inst,c);
endfunction
 
 
env e;
valid_wrrd_fixed vwrrdfx;
valid_wrrd_incr  vwrrdincr;
valid_wrrd_wrap  vwrrdwrap;
err_wrrd_fix     errwrrdfix;
rst_dut rdut; 
  
virtual function void build_phase(uvm_phase phase);
super.build_phase(phase);
   e       = env::type_id::create("env",this);
  vwrrdfx = valid_wrrd_fixed::type_id::create("vwrrdfx");
  vwrrdincr = valid_wrrd_incr::type_id::create("vwrrdincr");
  vwrrdwrap = valid_wrrd_wrap::type_id::create("vwrrdwrap");
  errwrrdfix = err_wrrd_fix::type_id::create("errwrrdfix");
  rdut       = rst_dut::type_id::create("rdut");
endfunction
 
virtual task run_phase(uvm_phase phase);
phase.raise_objection(this);
//rdut.start(e.a.seqr);
//#20;
//vwrrdfx.start(e.a.seqr);
//#20;
//vwrrdincr.start(e.a.seqr);
//#20;
//vwrrdwrap.start(e.a.seqr);
//#20;
errwrrdfix.start(e.a.seqr);
#20;
 
phase.drop_objection(this);
endtask
endclass
 
/////////////////////////////////////////////////////////////////////
 
module tb;
 
 axi_if vif();
 axi_slave dut (vif.clk, vif.resetn, vif.awvalid, vif.awready,  vif.awid, vif.awlen, vif.awsize, vif.awaddr,  vif.awburst, vif.wvalid, vif.wready, vif.wid, vif.wdata, vif.wstrb, vif.wlast, vif.bready, vif.bvalid, vif.bid, vif.bresp , vif.arready, vif.arid, vif.araddr, vif.arlen, vif.arsize, vif.arburst, vif.arvalid, vif.rid, vif.rdata, vif.rresp,vif.rlast,  vif.rvalid, vif.rready);
 
  initial begin
    vif.clk <= 0;
  end
  
  always #5 vif.clk <= ~vif.clk;
  
    initial begin
    uvm_config_db#(virtual axi_if)::set(null, "*", "vif", vif);
    run_test("test");
   end
  
  
  
  
    initial begin
    $dumpfile("dump.vcd");
    $dumpvars;   
  end
  
  assign vif.next_addrwr = dut.nextaddr;
  assign vif.next_addrrd = dut.rdnextaddr;
  
endmodule
```
