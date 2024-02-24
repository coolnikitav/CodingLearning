# Communication protocol: verification of serial peripheral interface

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/0f635505-eb34-4285-97ce-41f7f2f1b6f7)

Master pulls the CS line low to indicate to the slave that the data is incoming.

![image](https://github.com/coolnikitav/coding-lessons/assets/30304422/eede88be-fe6b-4acf-bfda-759f278c8fbc)

```
module spi(
  input clk, newd, rst,
  input [11:0] din,
  output reg sclk, cs, mosi
);
  typedef enum bit [1:0] {idle = 2'b00, enable = 2'b01, send 2'b10, comp = 2'b11} state_type;
  state_type state = idle;
  
  int countc = 0;
  int count = 0;
  
  // generation of sclk
  always @ (posedge clk) begin
    if (rst == 1'b1) begin
      countc <= 0;
      sclk <= 1'b0;
    end
    else begin
      if (countc < 10) begin  // sclk = clk / 20
        countc <= countc + 1;
      end
      else begin
        countc <= 0;
        sclk <= ~sclk;
      end
    end
  end
  
  // state machine
  reg [11:0] temp;
  
  always @ (posedge sclk) begin
    if (rst == 1'b1) begin
      cs <= 1'b1;
      mosi <= 1'b0;
    end
    else begin
      case (state)
        idle: begin
            if (newd == 1'b1) begin
              state <= send;
              temp <= din;
              cs <= 1'b0;
            end
            else begin
              state <= idle;
              temp <= 8'h00;
            end
        end
        send: begin
            if (count < 12) begin  // sending 12 bits
              mosi <= temp[count];  // sending LSB first
              count <= count + 1;
            end
            else begin
              count <= 0;
              state <= idle;
              cs <= 1'b1;
              mosi <= 1'b0;
            end
        end
        default: state <= idle;
      endcase
    end
  end  
endmodule

interface spi_if;
  logic clk, newd, rst;
  logic [11:0] din;
  logic sclk, cs, mosi;
endinterface
```
