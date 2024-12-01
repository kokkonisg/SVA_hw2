module fifo_prop #(parameter WIDTH = 16, parameter DEPTH = 16) (
    input   logic clk, rst_, fifo_write, fifo_read, fifo_full, fifo_empty,
    logic [WIDTH-1:0] fifo_data_in, fifo_data_out,
    logic [$clog2(DEPTH)-1:0] wr_ptr, rd_ptr,
    integer cnt
);

//reset behaviour check
property p1;
    @(posedge clk) !rst_ |-> wr_ptr==0 && rd_ptr==0 && cnt==0 && !fifo_full && fifo_empty;
endproperty

//empty fifo check
property p2; disable iff (!rst_)
    @(posedge clk) cnt==0 |-> fifo_empty;
endproperty

//full fifo check
property p3; disable iff (!rst_)
    @(posedge clk) cnt>=DEPTH |-> fifo_full;
endproperty

//only write while full check
property p4; disable iff (!rst_)
    @(posedge clk) fifo_full && fifo_write && !fifo_read |-> ##1 wr_ptr==$past(wr_ptr);
endproperty

//only read while full check
property p5; disable iff (!rst_)
    @(posedge clk) fifo_empty && fifo_read && !fifo_write |-> ##1 rd_ptr==$past(rd_ptr);
endproperty

//normal write check
property p6; disable iff (!rst_)
    @(posedge clk) fifo_write && !fifo_read |->
        if (!fifo_full) ##1 wr_ptr==$past(wr_ptr)+1'b1 && cnt==$past(cnt)+1;
endproperty

//normal read check
property p7; disable iff (!rst_)
    @(posedge clk) fifo_read && !fifo_write|-> 
        if (!fifo_empty) ##1 rd_ptr==$past(rd_ptr)+1'b1 && cnt==$past(cnt)-1;
endproperty

//read and write check
property p8; disable iff (!rst_)
    @(posedge clk) fifo_write && fifo_read |-> 
        if (!fifo_full && !fifo_empty) 
            ##1  wr_ptr==$past(wr_ptr)+1'b1 && rd_ptr==$past(rd_ptr)+1'b1 && cnt==$past(cnt)
        else if (fifo_empty)
            ##1 wr_ptr==$past(wr_ptr)+1'b1 && rd_ptr==$past(rd_ptr) && cnt==$past(cnt)+1
        else if (fifo_full)
            ##1 wr_ptr==$past(wr_ptr) && rd_ptr==$past(rd_ptr)+1'b1 && cnt==$past(cnt)-1;
endproperty

rstPr: assert property (p1) $display("\t%t  rstPr PASS",$stime);
    else $display("\t%t  rstPr FAIL",$stime);
emPr: assert property (p2) $display("\t%t   emPr PASS",$stime);
    else $display("\t%t   emPr FAIL",$stime);
flPr: assert property (p3) $display("\t%t   flPr PASS",$stime);
    else $display("\t%t   flPr FAIL",$stime);
flwrPr: assert property (p4) $display("\t%t flwrPr PASS",$stime);
    else $display("\t%t flwrPr FAIL",$stime);
emrdPr: assert property (p5) $display("\t%t emrdPr PASS",$stime);
    else $display("\t%t emrdPr FAIL",$stime);
wrPr: assert property (p6) $display("\t%t   wrPr PASS",$stime);
    else $display("\t%t   wrPr FAIL",$stime);
rdPr: assert property (p7) $display("\t%t   rdPr PASS",$stime);
    else $display("\t%t   rdPr FAIL",$stime);
wrrdPr: assert property (p8) $display("\t%t wrrdPr PASS",$stime);
    else $display("\t%t wrrdPr FAIL",$stime);

endmodule
