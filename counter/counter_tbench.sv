module counter_tbench;
logic clk, rst_, ld_cnt, updn_cnt, count_enb;
logic [15:0] data_in, data_out;

counter U1(.*);
bind U1 counter_prop bindU1 (.*);

always begin
    clk=0;
    forever begin
        #2 clk = ~clk;
    end
end

initial begin
    @(posedge clk) rst_ <= 1;
    #1 rst_ <= 0;count_enb<=0;ld_cnt<=1;
    @(posedge clk) rst_ <= 1;
    repeat(2) @(posedge clk);
    @(negedge clk) count_enb <= 1; updn_cnt <= 1;
    repeat(2) @(posedge clk);
    @(negedge clk) count_enb <= 1; updn_cnt <= 0;
    repeat(4) @(posedge clk);
    @(negedge clk) count_enb <= 1; updn_cnt <= 1;
    repeat(4) @(posedge clk);
    @(negedge clk) rst_ <= 0;
    @(negedge clk) rst_ <= 1;
    repeat(2) @(posedge clk);
    @(negedge clk) ld_cnt <= 0; data_in <= 16'h2;
    @(negedge clk) ld_cnt <= 1;
    repeat(2) @(posedge clk);
    @(negedge clk) count_enb <= 0;
    repeat(2) @(posedge clk);
    @(negedge clk) ld_cnt <= 0; data_in <= 16'hFFFF_FFFF;
    @(negedge clk) ld_cnt <= 1;
    repeat(2) @(posedge clk);
    @(posedge clk) rst_<=0;
    @(posedge clk) rst_<=1;
end

endmodule
