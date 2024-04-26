module extension(
    input  [15:0] IR,
    output [15:0] imm5,
    output [15:0] offset6,
    output [15:0] offset9,
    output [15:0] offset11
    );
    
    assign imm5     = { {11{IR[4]}},  IR[4:0]  };
    assign offset6  = { {10{IR[5]}},  IR[5:0]  };
    assign offset9  = {  {7{IR[8]}},  IR[8:0]  };
    assign offset11 = {  {5{IR[10]}}, IR[10:0] };
endmodule
