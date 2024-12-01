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
