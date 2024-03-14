# Bus Protocol: Verification of AXI Memory
AXI -  Advanced eXtensible Interface

AXI is a more general interface to a RAM
- Reads and writes can have variable latencies
- Write address and data can be sent at different times
- Reads and writes might not be issuable every cycle
- The user might not be ready to receive data every cycle
- Reads and writes can fail
- Reads and writes are issued in streams called bursts

5 groups of ports:

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/df95adc5-54f1-4fab-9ee8-c5687b72308a)

### Read Bursts

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/cff1f714-638c-4289-8c07-c1747b560198)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/102c56aa-9f0b-41ff-be30-5da47755773f)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/905bd1ca-bb22-4d95-8c12-dde5c15a5c65)

arready is set to 1 when memory is ready to receive a new burst

user sets arvalid to 1 when they are ready to issue a new burst

when arready and arvalid are 1, transaction is acknowledged and it starts

when receiver of the data is ready, it will set rready to 1

when memory chunk is ready to be sent out, the memory will set rvalid to 1

when rready and rvalid are 1, the handshake takes place

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f1e55af6-0fc2-4320-a541-3b72a92c8f21)

arburst indicates the type of burst

araddr is the start address of the burst

arlen is the num of transfers in the burst minus one

arsize indicates how many bytes are in each transfer

rdata contains the actual data requested

rresp indicates whether the read actually succeeded

rlast is a flag that indicates whether the current piece of data coming out is last in a given burst

### Example
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/80f250d1-6597-4db7-a9dd-d3f7290598eb)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/1324fba5-97cd-4883-a53f-7ec7dd757c72)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/f11eb0e4-7a1e-4176-a84a-618ad2112d2c)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/57d10b75-f1b3-49e9-9946-00d8da567559)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/c8aada23-b3cd-4395-9927-5907035f5c86)

### Write Bursts

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/a8bb312e-033c-4789-930a-8863f4b97d65)

write_strb determines which bytes of the data you want to set

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/ff18863d-5d5f-447f-8430-85f2757557b2)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/50f3617a-221e-4dee-9e32-8e6a3b7f7c2a)

awlen - number of transfers in the burst

wstrb has 1 bit for each byte in the wdata

### Example
![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/44d445f4-aeaf-4969-b718-a425c1cf3991)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/da596a31-f2cb-4bd7-b039-106cec9af111)

### AXI

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0208627f-0ec9-4cfd-9e0b-b33cd1ea3439)

### Burst
Fixed

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/33240be8-4aa7-4e26-8152-20003c9b178f)

Increment

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/760c59fe-cae9-40d2-bb54-fac34cd48051)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/854fcba8-e238-4d31-92f2-7a85b8012dc4)

Wrap

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/7238367b-fe20-4ff1-ac73-747b18e61a79)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/691d435c-1186-4a12-8fdb-66459e47675d)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/69ca2cb7-040e-41ba-a43a-67fc3f45dace)

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/200faa0a-2118-47be-93c7-92c58a2710b1)

Summary

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/fe4ae607-9591-416e-858e-b265fe16d315)

```
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
  logic [31:0] addr_wrapwr;
  logic [31:0] addr_wraprd;
  
endinterface 
 
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
        awnext_state  = awidle; 
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
               end
              else if (wlen_count != (awlen + 1 ))
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
          else 
          begin
           wnext_state = wvalids;
           wready      = 1'b1;
          end
          
          
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
       
       if(wlen_count != (awlen + 1))
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
       if( (awaddr < 128 ) && (awsize <= 3'b011) )
         bresp = 2'b00;  ///okay
       else if (awsize > 3'b011)
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
               if(rdfirst == 0) begin
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
      else if ( (araddr > 128) && ( arsize <= 3'b010) ) begin 
        rresp = 2'b11;  
        rnext_state = rerror; 
      end
      else if (arsize > 3'b010) begin
        rresp = 2'b10;
        rnext_state = rerror;
       end  
   
  end
  
   rwait: begin
      rvalid = 1'b0;
      len_count = len_count + 1;
     if(rready == 1'b1)
        begin
           rnext_state = rvalids; 
          if(len_count == (arlen + 1))
            rlast = 1'b1;
          else
            rlast = 1'b0;  
      end
       else
         rnext_state = rwait;
   end
   
   rvalids: begin
       
       if(len_count == (arlen + 1))
       begin
        rnext_state = ridle;
       end
       else
         begin
        rnext_state = rstart;
         end 
   end
   
   rerror : begin 
       len_count = len_count + 1;
       if(len_count == (arlen + 1))
       begin
        rnext_state = rvalids;
        rlast = 1'b1;
       end
       else
         begin
        rlast = 1'b0; 
        rnext_state = rstart;
         end 
   
   
   end 
 endcase
 end
endmodule
```
```
/////////////////////////Testbench Components
/////////////////////////////////////////////////
 
class transaction;
  
  rand bit [3:0] id;
  
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
 
 /* 
  constraint adr_c {
   awvalid == 0;
   arvalid == 1; 
  
  }
  */
  
  constraint valid_c {
   arvalid != awvalid;
  }
  
  constraint addr_c {
   awaddr == 5;
  //awaddr > 0; awaddr < 15;
   
  }
  
  constraint awsize_c {
  
  awsize >= 0; awsize < 3;
  }
  
  constraint awburst_c {
   awburst == 2;
  //awburst >= 0; awburst < 3; 
  }
  
  
  constraint arlen_c {
    arlen > 0; arlen <= 7;
  }
  
  
  constraint araddr_c {
    araddr == 5;
   // araddr > 0; araddr <= 7;
  }
  
  constraint arburst_c {
  arburst == 2;
  //arburst >= 0; arburst < 3; 
  }
  
endclass
 
 
 
//////////////////////////////////
class generator;
  
  transaction tr;
  mailbox #(transaction) mbxgd;
  
  event done; ///gen completed sending requested no. of transaction
  event drvnext; /// dr complete its wor;
  event sconext; ///scoreboard complete its work
 
   int count = 0;
  
  function new( mailbox #(transaction) mbxgd);
    this.mbxgd = mbxgd;   
    tr =new();
  endfunction
  
    task run();
    
    for(int i=0; i <= count; i++) begin
      assert(tr.randomize) else $error("Randomization Failed"); 
      
      if(tr.awburst == 2'b10)
        begin
          tr.awlen = 4'b0111;
        end
      
      
      if(tr.arburst == 2'b10)
        begin
          tr.arlen = 4'b0111;
        end
      
     // $display("[GEN] : WRITE : %0b READ : %0b BURST MODE : %0d",tr.awvalid, tr.arvalid, tr.awburst);
      $display("[GEN] : WR :%0b RD:%0b WRBUR : %0d RDBUR: %0d WRADDR :%0d RDADDR : %0d WLEN :%0d RLEN :%0d",tr.awvalid, tr.arvalid, tr.awburst, tr.arburst, tr.awaddr, tr.araddr, tr.awlen, tr.arlen);
      mbxgd.put(tr);
      @(drvnext);
      @(sconext);
    end
    ->done;
  endtask
  
   
endclass
 
 
/////////////////////////////////////
 
 
class driver;
  
  virtual axi_if vif;
  
  transaction tr;
  
  event drvnext;
  event monnext;
  
  mailbox #(transaction) mbxgd;
 
  
  function new( mailbox #(transaction) mbxgd );
    this.mbxgd = mbxgd; 
  endfunction
  
  //////////////////Resetting System
  task reset();
    
     vif.resetn <= 1'b0;
      
     vif.awvalid <= 1'b0;
     vif.awid <= 0;
     vif.awlen <= 0;
     vif.awsize <= 0;
     vif.awaddr <= 0;
     vif.awburst <= 0;
     
     vif.wvalid <= 0;
     vif.wid <= 0;
     vif.wdata <= 0;
     vif.wstrb <= 0;
     vif.wlast <= 0;
    
     vif.bready <= 0;
 
    
     vif.arvalid <= 1'b0;
     vif.arid <= 0;
     vif.arlen <= 0;
     vif.arsize <= 0;
     vif.araddr <= 0;
     vif.arburst <= 0;
    
    repeat(5) @(posedge vif.clk);
    vif.resetn <= 1'b1;
    $display("[DRV] : RESET DONE"); 
  endtask
  
  
  ///////////////////////////////write data in Fixed Mode 
  task fixed_write(input transaction tr);
      int len = 0;
      len = tr.awlen + 1;  //8
      $display("[DRV] : FIXED MODE -> DATA WRITE DONE");
      @(posedge vif.clk);     
      vif.resetn <= 1'b1;
      vif.awvalid <= 1'b1;
      vif.arvalid <= 1'b0;  ////disable read
      vif.awid    <= tr.id;
      vif.awlen   <= tr.awlen;
      vif.awsize  <= 3'b010;   ///4 byte 
      vif.awburst <= 2'b00;   //00
      vif.wvalid <= 1'b1;
      vif.wid    <= tr.id; 
      vif.wstrb  <= 4'b1111;
      vif.bready <= 1'b1;
      vif.awaddr  <= tr.awaddr;
      vif.wdata  <= $urandom_range(1,100);
      
      @(posedge vif.wready);
      @(posedge vif.clk);
    
    
    for(int i = 1; i< len ; i++) begin /// 1 2 3 4 5 6 7
      vif.awaddr  <= tr.awaddr;
      vif.wdata  <= $urandom_range(1,100);
      @(posedge vif.wready);
      @(posedge vif.clk);
      end
      
      vif.wlast  <= 1'b1;
      vif.awvalid <= 1'b0;
      vif.arvalid <= 1'b0;
      vif.wvalid   <= 1'b0;
      @(posedge vif.clk);
      vif.wlast  <= 1'b0;
      @(negedge vif.bvalid);
      ->drvnext;
     endtask
  
  ///////////////////////////Write data in Incr Mode //////
   
  task incr_write(input transaction tr);
      int len = 0;
      len = tr.awlen + 1;  //8
       $display("[DRV] : INCR MODE -> DATA WRITE DONE");
      @(posedge vif.clk);
      vif.resetn <= 1'b1;
      vif.arvalid <= 1'b0; ////disable read 
      vif.awvalid <= 1'b1;
      vif.awid    <= tr.id;
      vif.awlen   <= tr.awlen;
      vif.awsize  <= 3'b010;    
      vif.awburst <= 2'b01;   
      vif.wvalid <= 1'b1;
      vif.wid    <= tr.id; 
      vif.wstrb  <= 4'b1111;
      vif.bready <= 1'b1;
      vif.awaddr  <= tr.awaddr;
      vif.wdata  <= $urandom_range(1,100);
      
      @(posedge vif.wready);
      @(posedge vif.clk);
    
   for(int i = 1; i< len; i++) begin  ///i < 8  1 2 3 4 5 6 7
      vif.awaddr  <= tr.awaddr + 4*i;
      vif.wdata  <= $urandom_range(1,100);
      @(posedge vif.wready);
      @(posedge vif.clk);
    end
      
      vif.wlast   <= 1'b1;  
      vif.awvalid <= 1'b0;
      vif.arvalid <= 1'b0;
      vif.wvalid  <= 1'b0;
      @(posedge vif.clk);
      vif.wlast  <= 1'b0;
      @(negedge vif.bvalid);
   
    
      ->drvnext;
     endtask
  
  
  
  
  
  
   //////////////////////////////Write data in Wrap Mode
  
    task wrap_write(input transaction tr);
      int len = 0;
      len = tr.awlen + 1;  //8
      $display("[DRV] : WRAP MODE -> DATA WRITE DONE");
      @(posedge vif.clk);
      vif.arvalid <= 1'b0;  ///disable read
      vif.resetn <= 1'b1;
      vif.awvalid <= 1'b1;
      vif.awid    <= tr.id;
      vif.awlen   <= tr.awlen;
      vif.awsize  <= 3'b010;    
      vif.awburst <= 2'b10;   
      vif.wvalid <= 1'b1;
      vif.wid    <= tr.id; 
      vif.wstrb  <= 4'b1111;
      vif.bready <= 1'b1;
      
      
      vif.awaddr <= tr.awaddr;
      vif.wdata  <= $urandom_range(1,100);
      @(posedge vif.wready);
      @(posedge vif.clk);
    
      for(int i = 0; i < 7; i++) begin  ///0 1 2 3 4 5 6
      vif.awaddr  <= vif.addr_wrapwr;
      vif.wdata  <= $urandom_range(1,100);
      @(posedge vif.wready);
      @(posedge vif.clk);
      end
      
      vif.wlast  <= 1'b1;  
      @(posedge vif.clk);
      vif.wlast  <= 1'b0;
      vif.awvalid <= 1'b0;
      vif.arvalid <= 1'b0;
      vif.wvalid  <= 1'b0;
      @(negedge vif.bvalid);
   
      ->drvnext;
     endtask
  
  /////////////////////////////////read fixed mode
  
  task fixed_read(input transaction tr);
    
    int len = 0;
    len = tr.arlen + 1; //8
    $display("[DRV] : FIXED MODE -> DATA READ");
      @(posedge vif.clk);
      vif.awvalid <= 1'b0;  /////disable write transaction
      vif.resetn  <= 1'b1;
      vif.arvalid <= 1'b1;
      vif.arid    <= tr.id;
      vif.arlen   <= tr.arlen;
      vif.arsize  <= 3'b010;    
      vif.arburst <= 2'b00;
      vif.rready  <= 1'b1;
        
      for(int i = 0; i < len; i++) begin // 0 1  2 3 4 5 6 7
       vif.araddr  <= tr.araddr;
       @(posedge vif.arready);
       @(posedge vif.clk);
      end
       
     @(negedge vif.rlast);
     vif.arvalid <= 1'b0;
     vif.rready  <= 1'b0;
     
    ->drvnext;
    
    
    
  endtask
  
  
  
  ///////////////////////////////read incr mode
  
    task incr_read(input transaction tr);
      
      int len = 0;
      len = tr.arlen + 1;
      $display("[DRV] : INCR MODE -> DATA READ");
      @(posedge vif.clk);
      vif.awvalid <= 1'b0;  /////disable write transaction
      vif.resetn  <= 1'b1;
      vif.arvalid <= 1'b1;
      vif.arid    <= tr.id;
      vif.arlen   <= tr.arlen;
      vif.arsize  <= 3'b010;    
      vif.arburst <= 2'b01;
      vif.rready  <= 1'b1;
      
  
        
      for(int i = 0; i< len; i++) begin
       vif.araddr  <= tr.araddr + 4*i;
       @(posedge vif.arready);
       @(posedge vif.clk);
      end
       
     @(negedge vif.rlast);
     vif.arvalid <= 1'b0;
     vif.rready  <= 1'b0;
      
     ->drvnext;
    
    
    
  endtask
  
  
  
  //////////////////////////////////////////wrap mode
  
    task wrap_read(input transaction tr);
    
      int len = 0;
      len = 8;
      $display("[DRV] : WRAP MODE -> DATA READ COMPLETE");
      @(posedge vif.clk);
      vif.awvalid <= 1'b0;  /////disable write transaction
      vif.resetn  <= 1'b1;
      vif.arvalid <= 1'b1;
      vif.arid    <= tr.id;
      vif.arlen   <= 4'b0111;
      vif.arsize  <= 3'b010;    
      vif.arburst <= 2'b10;
      vif.rready  <= 1'b1;     
      vif.araddr  <= tr.araddr;
      @(posedge vif.rvalid);
      @(posedge vif.clk);
      
 
  
        
      for(int i = 0; i< 7; i++) begin /// 0123456  
        vif.araddr  <= vif.addr_wraprd;      
        @(posedge vif.rvalid);
        @(posedge vif.clk);
      end
       
     @(negedge vif.rlast);
     vif.arvalid <= 1'b0;
     vif.rready  <= 1'b0;
 
     ->drvnext;
    
  endtask
  
  
  
 
  
  ///////////////////////////////////////////////////////main task
  
  
  task run();
    
    forever begin
             
      mbxgd.get(tr);
     /////////////////////////write mode check and sig gen 
      if(tr.awvalid == 1'b1) begin
              if(tr.awburst == 2'b00)
                begin
                 fixed_write(tr);
                end
              else if (tr.awburst == 2'b01)
                begin
                incr_write(tr);
                end
              else if (tr.awburst == 2'b10)
                begin
                wrap_write(tr);
                end
 
      end   
     
     
   /////////////////////////////read mode check and sig gen
      
       if(tr.arvalid == 1'b1) begin
                 if(tr.arburst  == 2'b00)
                begin
                  fixed_read(tr);
                end
            else if (tr.arburst == 2'b01)
                begin
                incr_read(tr);
                end
            else if (tr.arburst == 2'b10)
                begin
                wrap_read(tr);
                end
                
          end  
    end
  endtask
  
    
  
endclass
///////////////////////////////////////////////////////
 
/*
module tb;
   
  generator gen;
  driver drv;
  event next;
  event done;
  
  mailbox #(transaction) mbxgd;
  
  axi_if vif();
  axi_slave dut (vif.clk, vif.resetn, vif.awvalid, vif.awready,  vif.awid, vif.awlen, vif.awsize, vif.awaddr,  vif.awburst, vif.wvalid, vif.wready, vif.wid, vif.wdata, vif.wstrb, vif.wlast, vif.bready, vif.bvalid, vif.bid, vif.bresp , vif.arready, vif.arid, vif.araddr, vif.arlen, vif.arsize, vif.arburst, vif.arvalid, vif.rid, vif.rdata, vif.rresp,vif.rlast,  vif.rvalid, vif.rready);
 
  initial begin
    vif.clk <= 0;
  end
  
  always #5 vif.clk <= ~vif.clk;
  
  initial begin
 
    mbxgd = new();
    gen = new(mbxgd);
    drv = new(mbxgd);
    gen.count = 5;
    drv.vif = vif;
    
    drv.drvnext = next;
    gen.drvnext = next;
    
  end
  
  initial begin
    drv.reset();
    fork
      gen.run();
      drv.run();
    join_none  
    wait(gen.done.triggered);
    $finish();
  end
   
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;   
  end
 
assign vif.addr_wrapwr = dut.nextaddr;
assign vif.addr_wraprd = dut.rdretaddr;  
 
 
endmodule
 
*/
 
 
///////////////////////////////////////////////////
 
 
class monitor;
    
  virtual axi_if vif;
 
  
  transaction tr;
 
  event sconext;
  int len = 0;
  
  mailbox #(transaction) mbxms;
 
 
  
 
  
  function new( mailbox #(transaction) mbxms );
    this.mbxms = mbxms;
  endfunction
  
  
  task run();
    
    tr = new();
    
    forever 
      begin
        
        
      @(posedge vif.clk);
        
      //////////////////////////write logic  
        
    if(vif.awvalid == 1'b1) begin 
         len = vif.awlen + 1;  
         tr.awvalid = vif.awvalid;
         tr.arvalid = vif.arvalid;
         
         
      for(int i = 0; i< len; i++) begin
       @(posedge vif.wready); 
       @(posedge vif.clk);
       tr.awaddr = vif.awaddr;
       tr.wdata  = vif.wdata;
       tr.awburst = vif.awburst;   
       mbxms.put(tr);
       $display("[MON] : ADDR : %0x DATA : %0x BURST TYPE : %0d",tr.awaddr, tr.wdata, tr.awburst);    
      end
       
      @(posedge vif.clk);
      @(negedge vif.bvalid);
      @(posedge vif.clk);
      $display("[MON] : Transaction Complete");  
   end
 
     /////////////////////read logic   
        
       if(vif.arvalid == 1'b1)
        begin
         len = vif.arlen + 1;    
         tr.awvalid = vif.awvalid;
         tr.arvalid = vif.arvalid;
         
     
      for(int i = 0; i< len; i++) begin  
       @(posedge  vif.rvalid);
       @(posedge vif.clk);
       tr.rdata  = vif.rdata;
       tr.arburst = vif.arburst;
       tr.araddr = vif.araddr;
       mbxms.put(tr); 
       $display("[MON] : ADDR : %0x DATA : %0x BURST TYPE : %0d",tr.araddr, tr.rdata, tr.arburst);
       end
       
      @(posedge vif.clk);
      @(negedge vif.rlast);
      @(posedge vif.clk);
      $display("[MON] : Transaction Complete");
      end
       ->sconext; 
      end 
  endtask
 
  
  
endclass
 
///////////////////////////////////////
 
 
class scoreboard;
  
  transaction tr;
 
  
  mailbox #(transaction) mbxms;
  
 
  
  bit [31:0] temp;
  
  bit [7:0] data[128] = '{default:0};
  
  int count = 0;
  int len   = 0;
  
 
  
  function new( mailbox #(transaction) mbxms );
    this.mbxms = mbxms;
  endfunction
  
  
  task run();
    
    forever 
      begin  
        
      
      mbxms.get(tr);
 
      
     if(tr.awvalid == 1'b1) begin
        data[tr.awaddr]     = tr.wdata[7:0];
        data[tr.awaddr + 1] = tr.wdata[15:8];
        data[tr.awaddr + 2] = tr.wdata[23:16];
        data[tr.awaddr + 3] = tr.wdata[31:24]; 
        
        $display("[SCO] : DATA STORED ADDR :%0x and DATA :%0x", tr.awaddr, tr.wdata[7:0]);
        end     
        
        if(tr.arvalid == 1'b1) begin
            temp = {data[tr.araddr + 3],data[tr.araddr + 2],data[tr.araddr + 1],data[tr.araddr] };
           
        $display("[SCO] : DATA READ ADDR :%0x and DATA :%0x MEM :%0x", tr.araddr, tr.rdata, temp);
          if(tr.rdata == 32'hc0c0c0c) 
          begin
           $display("[SCO] : DATA MATCHED : EMPTY LOCATION");
          end
          else if (tr.rdata == temp)
          begin
           $display("[SCO] : DATA MATCHED");
          end
          else
           begin
           $display("[SCO] : DATA MISMATCHED");
           end
       
        end
        
     
    end
  endtask
  
  
endclass
 
 
///////////////////////////////////////////////////
 
 module tb;
   
  monitor mon; 
  generator gen;
  driver drv;
  scoreboard sco;
   
   
  event nextgd;
  event nextgm;
  
 
  
  mailbox #(transaction) mbxgd, mbxms;
  
  axi_if vif();
  axi_slave dut (vif.clk, vif.resetn, vif.awvalid, vif.awready,  vif.awid, vif.awlen, vif.awsize, vif.awaddr,  vif.awburst, vif.wvalid, vif.wready, vif.wid, vif.wdata, vif.wstrb, vif.wlast, vif.bready, vif.bvalid, vif.bid, vif.bresp , vif.arready, vif.arid, vif.araddr, vif.arlen, vif.arsize, vif.arburst, vif.arvalid, vif.rid, vif.rdata, vif.rresp,vif.rlast,  vif.rvalid, vif.rready);
 
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
    
    gen.count = 4;
    drv.vif = vif;
    mon.vif = vif;
    
    drv.drvnext = nextgd;
    gen.drvnext = nextgd;
    
    gen.sconext = nextgm;
    mon.sconext = nextgm;
    
  end
  
  initial begin
    drv.reset();
    fork
      gen.run();
      drv.run();
      mon.run();
      sco.run();
    join_any  
    wait(gen.done.triggered);
    $finish;
  end
   
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;   
  end
 
assign vif.addr_wrapwr = dut.retaddr;
assign vif.addr_wraprd = dut.rdretaddr;  
   
endmodule
```
```
# KERNEL: [DRV] : RESET DONE
# KERNEL: [GEN] : WR :0 RD:1 WRBUR : 2 RDBUR: 2 WRADDR :5 RDADDR : 5 WLEN :7 RLEN :7
# KERNEL: [DRV] : WRAP MODE -> DATA READ COMPLETE
# KERNEL: [MON] : ADDR : 5 DATA : c0c0c0c BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :5 and DATA :c0c0c0c MEM :0
# KERNEL: [SCO] : DATA MATCHED : EMPTY LOCATION
# KERNEL: [MON] : ADDR : 9 DATA : c0c0c0c BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :9 and DATA :c0c0c0c MEM :0
# KERNEL: [SCO] : DATA MATCHED : EMPTY LOCATION
# KERNEL: [MON] : ADDR : d DATA : c0c0c0c BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :d and DATA :c0c0c0c MEM :0
# KERNEL: [SCO] : DATA MATCHED : EMPTY LOCATION
# KERNEL: [MON] : ADDR : 11 DATA : c0c0c0c BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :11 and DATA :c0c0c0c MEM :0
# KERNEL: [SCO] : DATA MATCHED : EMPTY LOCATION
# KERNEL: [MON] : ADDR : 15 DATA : c0c0c0c BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :15 and DATA :c0c0c0c MEM :0
# KERNEL: [SCO] : DATA MATCHED : EMPTY LOCATION
# KERNEL: [MON] : ADDR : 19 DATA : c0c0c0c BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :19 and DATA :c0c0c0c MEM :0
# KERNEL: [SCO] : DATA MATCHED : EMPTY LOCATION
# KERNEL: [MON] : ADDR : 1d DATA : c0c0c0c BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :1d and DATA :c0c0c0c MEM :0
# KERNEL: [SCO] : DATA MATCHED : EMPTY LOCATION
# KERNEL: [MON] : ADDR : 1 DATA : c0c0c0c BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :1 and DATA :c0c0c0c MEM :0
# KERNEL: [SCO] : DATA MATCHED : EMPTY LOCATION
# KERNEL: [MON] : Transaction Complete
# KERNEL: [GEN] : WR :1 RD:0 WRBUR : 2 RDBUR: 2 WRADDR :5 RDADDR : 5 WLEN :7 RLEN :7
# KERNEL: [DRV] : WRAP MODE -> DATA WRITE DONE
# KERNEL: [MON] : ADDR : 5 DATA : 5 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :5 and DATA :5
# KERNEL: [MON] : ADDR : 9 DATA : 1f BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :9 and DATA :1f
# KERNEL: [MON] : ADDR : d DATA : 11 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :d and DATA :11
# KERNEL: [MON] : ADDR : 11 DATA : 5f BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :11 and DATA :5f
# KERNEL: [MON] : ADDR : 15 DATA : e BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :15 and DATA :e
# KERNEL: [MON] : ADDR : 19 DATA : 3 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :19 and DATA :3
# KERNEL: [MON] : ADDR : 1d DATA : 19 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :1d and DATA :19
# KERNEL: [MON] : ADDR : 1 DATA : 57 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :1 and DATA :57
# KERNEL: [MON] : Transaction Complete
# KERNEL: [GEN] : WR :1 RD:0 WRBUR : 2 RDBUR: 2 WRADDR :5 RDADDR : 5 WLEN :7 RLEN :7
# KERNEL: [DRV] : WRAP MODE -> DATA WRITE DONE
# KERNEL: [MON] : ADDR : 5 DATA : 3c BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :5 and DATA :3c
# KERNEL: [MON] : ADDR : 9 DATA : 4e BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :9 and DATA :4e
# KERNEL: [MON] : ADDR : d DATA : 30 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :d and DATA :30
# KERNEL: [MON] : ADDR : 11 DATA : 44 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :11 and DATA :44
# KERNEL: [MON] : ADDR : 15 DATA : 51 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :15 and DATA :51
# KERNEL: [MON] : ADDR : 19 DATA : 37 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :19 and DATA :37
# KERNEL: [MON] : ADDR : 1d DATA : 4a BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :1d and DATA :4a
# KERNEL: [MON] : ADDR : 1 DATA : 12 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :1 and DATA :12
# KERNEL: [MON] : Transaction Complete
# KERNEL: [GEN] : WR :0 RD:1 WRBUR : 2 RDBUR: 2 WRADDR :5 RDADDR : 5 WLEN :7 RLEN :7
# KERNEL: [DRV] : WRAP MODE -> DATA READ COMPLETE
# KERNEL: [MON] : ADDR : 5 DATA : 3c BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :5 and DATA :3c MEM :3c
# KERNEL: [SCO] : DATA MATCHED
# KERNEL: [MON] : ADDR : 9 DATA : 4e BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :9 and DATA :4e MEM :4e
# KERNEL: [SCO] : DATA MATCHED
# KERNEL: [MON] : ADDR : d DATA : 30 BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :d and DATA :30 MEM :30
# KERNEL: [SCO] : DATA MATCHED
# KERNEL: [MON] : ADDR : 11 DATA : 44 BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :11 and DATA :44 MEM :44
# KERNEL: [SCO] : DATA MATCHED
# KERNEL: [MON] : ADDR : 15 DATA : 51 BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :15 and DATA :51 MEM :51
# KERNEL: [SCO] : DATA MATCHED
# KERNEL: [MON] : ADDR : 19 DATA : 37 BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :19 and DATA :37 MEM :37
# KERNEL: [SCO] : DATA MATCHED
# KERNEL: [MON] : ADDR : 1d DATA : 4a BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :1d and DATA :4a MEM :4a
# KERNEL: [SCO] : DATA MATCHED
# KERNEL: [MON] : ADDR : 1 DATA : 12 BURST TYPE : 2
# KERNEL: [SCO] : DATA READ ADDR :1 and DATA :12 MEM :12
# KERNEL: [SCO] : DATA MATCHED
# KERNEL: [MON] : Transaction Complete
# KERNEL: [GEN] : WR :1 RD:0 WRBUR : 2 RDBUR: 2 WRADDR :5 RDADDR : 5 WLEN :7 RLEN :7
# KERNEL: [DRV] : WRAP MODE -> DATA WRITE DONE
# KERNEL: [MON] : ADDR : 5 DATA : 35 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :5 and DATA :35
# KERNEL: [MON] : ADDR : 9 DATA : 31 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :9 and DATA :31
# KERNEL: [MON] : ADDR : d DATA : 5f BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :d and DATA :5f
# KERNEL: [MON] : ADDR : 11 DATA : 4d BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :11 and DATA :4d
# KERNEL: [MON] : ADDR : 15 DATA : 37 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :15 and DATA :37
# KERNEL: [MON] : ADDR : 19 DATA : 17 BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :19 and DATA :17
# KERNEL: [MON] : ADDR : 1d DATA : 2e BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :1d and DATA :2e
# KERNEL: [MON] : ADDR : 1 DATA : 3e BURST TYPE : 2
# KERNEL: [SCO] : DATA STORED ADDR :1 and DATA :3e
# KERNEL: [MON] : Transaction Complete
```
