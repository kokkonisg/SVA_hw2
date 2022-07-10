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

module counter_prop(
    input logic clk, rst_, updn_cnt, count_enb, ld_cnt,
    logic [15:0] data_in, data_out
);

property p1;
    @(posedge clk) !rst_ |-> data_out==0;
endproperty

property p2; disable iff (!rst_)
    @(posedge clk) !ld_cnt |-> ##1 data_out==data_in;
endproperty

property p3; disable iff (!rst_)
    @(posedge clk) ld_cnt && count_enb |-> 
        if (updn_cnt) ##1 data_out==$past(data_out) + 1'b1
        else if (!updn_cnt) ##1 data_out==$past(data_out) - 1'b1;
endproperty

property p4; disable iff (!rst_)
    @(posedge clk) ld_cnt && !count_enb |-> ##1 data_out==$past(data_out);
endproperty

rstPr: assert property (p1) $display("\t%t rstPr PASS",$stime);
    else $display("\t%t rstPr FAIL",$stime);
ldPr: assert property (p2) $display("\t%t  ldPr PASS",$stime);
    else $display("\t%t  ldPr FAIL",$stime);
enPr: assert property (p3) $display("\t%t  enPr PASS",$stime);
    else $display("\t%t  enPr FAIL",$stime);
nenPr: assert property (p4) $display("\t%t nenPr PASS",$stime);
    else $display("\t%t nenPr FAIL",$stime);

endmodule

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
    repeat(2) @(posedge clk);
    @(posedge clk) rst_ <= 1;
    #1 rst_ <= 0;count_enb<=0;ld_cnt<=1;
    #1 rst_ <= 1;
    repeat(4) @(posedge clk);
    @(posedge clk) count_enb <= 1; updn_cnt <= 1;
    repeat(4) @(posedge clk);
    @(posedge clk) count_enb <= 1; updn_cnt <= 0;
    repeat(2) @(posedge clk);
    @(posedge clk) count_enb <= 0; updn_cnt <= 1;
    repeat(4) @(posedge clk);
    repeat(4) @(posedge clk);
    @(posedge clk) rst_ <= 0;
    @(posedge clk) rst_ <= 1;
    @(posedge clk) count_enb <= 1; updn_cnt <= 1;
    @(posedge clk) count_enb <= 1; updn_cnt <= 1;
    @(negedge clk) count_enb <= 1; updn_cnt <= 0;
    @(negedge clk) count_enb <= 1; updn_cnt <= 0;
    @(posedge clk) count_enb <= 0; updn_cnt <= 1;
    @(posedge clk) ld_cnt <= 0; data_in <= 16'h2;
    @(posedge clk) ld_cnt <= 1;
    repeat(4) @(posedge clk);
    @(posedge clk) count_enb <= 1; updn_cnt <= 0;
    repeat(8) @(posedge clk);
    @(posedge clk) ld_cnt <= 0; data_in <= 16'hFFFF_FFFC; updn_cnt<=1;
    @(posedge clk) ld_cnt <= 1;
    repeat(8) @(posedge clk);
    @(posedge clk) count_enb <= 0; updn_cnt <= 1;
end

endmodule