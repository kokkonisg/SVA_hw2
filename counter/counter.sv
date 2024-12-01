module counter(
    input logic clk, rst_, updn_cnt, count_enb, ld_cnt,
    logic [15:0] data_in,
    output logic [15:0] data_out
);

    always_ff @(posedge clk, negedge rst_) begin
        if(!rst_) data_out <= 16'b0;
        else if(!ld_cnt) data_out <= data_in;
        else if(count_enb) begin
            if(updn_cnt) data_out <= data_out + 1'b1;
            else if(!updn_cnt) data_out <= data_out - 1'b1;
        end
    end
endmodule
