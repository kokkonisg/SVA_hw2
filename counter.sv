module counter(
    input logic clk, rst_, updn_cnt, count_enb, ld_cnt,
    logic [15:0] data_in,
    output logic [15:0] data_out
);

    always_ff @(posedge clk, posedge rst_) begin
        priority if(!rst_) data_out <= 16'b0;
        else if(!ld_cnt) data_out <= data_in;
        else if(count_enb) begin
            unique if(updn_cnt) data_out <= data_out + 1'b1;
            else if (!updn_cnt) data_out <= data_out - 1'b1;
        end
    end
endmodule

module counter_prop(
    input logic clk, rst_, updn_cnt, count_enb, ld_cnt,
    logic [15:0] data_in,
    output logic [15:0] data_out
);

property p1;
    @(posedge clk) rst_ |-> ##1 data_out==0;
endproperty

endmodule

module tbench;
logic clk, rst_, ld_cnt, updn_cnt, count_enb;
logic [15:0] data_in, data_out;

counter U1(.*);

initial begin
    clk=0;
    forever begin
        #2 clk = ~clk;
    end
end

always begin
    repeat(4) @(posedge clk);
    @(posedge clk) rst_ <= 1;
    @(posedge clk) rst_ <= 0;
    @(posedge clk) rst_ <= 0;
    @(posedge clk) rst_ <= 1;
    repeat(4) @(posedge clk);
    @(posedge clk) count_enb <= 1; updn_cnt <= 1;
    repeat(4) @(posedge clk);
    @(posedge clk) count_enb <= 1; updn_cnt <= 0;
    repeat(2) @(posedge clk);
    @(posedge clk) count_enb <= 0; updn_cnt <= 1;
    repeat(4) @(posedge clk);
    repeat(4) @(posedge clk);
    @(posedge clk) rst_ <= 0;
    @(posedge clk) rst_ <= 0;
    @(posedge clk) rst_ <= 1;
    @(posedge clk) count_enb <= 1; updn_cnt <= 1;
    @(posedge clk) count_enb <= 0; updn_cnt <= 1;
    @(posedge clk) ld_cnt <= 0; data_in <= 16'hA;
    @(posedge clk) ld_cnt <= 1; data_in <= 16'hA;
    repeat(4) @(posedge clk);
    @(posedge clk) count_enb <= 1; updn_cnt <= 1;
    repeat(4) @(posedge clk);
    repeat(4) @(posedge clk);
    @(posedge clk) count_enb <= 0; updn_cnt <= 1;
end

endmodule