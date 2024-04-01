package e_w_control_pkg;
    function automatic logic [1:0] w_control (input bit [15:0] IR);
        if (IR[13:12] == 2'b01)
            return 2'b00;
        else if (IR[15:12] == 4'b1110)
            return 2'b10;
    endfunction
    
    function automatic logic [5:0] e_control (input bit [15:0] IR);
        if (IR[15:12] == 4'b0001) begin
            if (IR[5] == 1'b0)
                return 6'b00xxx1;
            else if (IR[5] == 1'b1)
                return 6'b00xxx0;
        end else if (IR[15:12] == 4'b0101) begin
            if (IR[5] == 1'b0)
                return 6'b01xxx1;   
            else if (IR[5] == 1'b1)
                return 6'b01xxx0;    
        end else if (IR[15:12] == 4'b1001) begin
            return 6'b10xxxx;
        end else if (IR[15:12] == 4'b1110) begin
            return 6'bxx011x;
        end
    endfunction
endpackage