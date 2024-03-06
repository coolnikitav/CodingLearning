# Bus Protocol: Verification of APB_RAM

Advanced Peripheral Bus Signals
- Used to communicate with peripheral components
- Single chanel

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/d613b276-df7d-4fe0-81a6-d80b089cd427)

Signals
- PCLK
- PRESETn - synch. reset
- PADDR - [31:0]
- PDATA - 8, 16, 32 bits
- PWRITE - 0 = READ, 1 = WRITE
- PSTRB - [3:0] - select which of the data bits are valid. 0 = [7:0], 1 = [15:8], 2 = [23:16], 3 = [31:24]
- PSEL - select slave
- PENABLE - enable
- PRDATA - [31:0] read data from slave
- PREADY - slave indicates when data is valid
- PSLVERR - slave error
- PPROT - [2:0], protection signal, 0 = priveleged/nonpriveleged, 1 = secure/nonsecure, 2 = data/control

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/71ad7e20-ba9b-4895-a1a2-396cfc6ba6f6)

```
module apb_ram
  (
    input resetn,
    input pclk,
    input psel,
    input penable,
    input pwrite,
    input [31:0] paddr, pwdata,
    output reg [31:0] prdata,
    output reg pready, plsverr
  );
  reg [31:0] mem [32];
  
  typedef enum {idle = 0, setup = 1, access = 2, transfer = 3} state_type;
  state_type state = idle, next_state = idle;
  
  always @ (posedge pclk) begin
    if (presetn == 1'b0) begin  // active low
      state <= idle;
      prdata <= 32'h0000_00000;
      pready <= 1'b0;
      pslverr <= 1'b0;
      
      for (int i = 0; i < 32; i++) begin
        mem[i] <= 0;
      end
    end else begin
      case (state)
        idle: begin
          prdata <= 32'h0000_0000;
          pready <= 1'b0;
          pslverr <= 1'b0;
          
          if ( (psel == 1'b0) && (penable == 1'b0) ) begin
            state <= setup;
          end
        end
        setup: begin  // start of transaction
          if ( (psel == 1'b0) && (penable == 1'b0) ) begin
            if (paddr < 32) begin
              state <= access;
              pready <= 1'b0;
            end else begin
              state <= access;
              pready <= 1'b0;
            end
          end else begin
            state <= setup;
          end
        end
        access: begin
          if (psel && pwrite && penable) begin
            if (paddr < 32) begin
              mem[paddr] <= pwdata;
              state <= transfer;
              pslverr <= 1'b0;
            end else begin
              state <= transfer;
              pready <= 1'b1;
              pslverr <= 1'b1;
            end
          end else if (psel && !pwrite && penable) begin
            if (paddr < 32) begin
              prdata <= mem[paddr];
              state <= transfer;
              pready <= 1'b1;
              pslverr <= 1'b0;
            end else begin
              state <= transfer;
              pready <= 1'b1;
              pslverr <= 1'b1;
              prdata <= 32'hxxxx_xxxx;
            end
          end
        end
        transfer: begin
          state <= setup;
          pready <= 1'b0;
          pslverr <= 1'b0;
        end
        default: state <= idle;        
      endcase
    end
  end
endmodule
```
