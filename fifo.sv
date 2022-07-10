module fifo #(parameter WIDTH = 16, parameter DEPTH = 16) (
    input   logic clk, rst_, fifo_write, fifo_read, 
    output  logic fifo_full, fifo_empty,
    input   logic [WIDTH-1:0] fifo_data_in,
    output  logic [WIDTH-1:0] fifo_data_out
);

    logic [$clog2(DEPTH)-1:0] wr_ptr, rd_ptr;
    integer cnt;
    logic [WIDTH-1:0] FIFO [DEPTH];

    always_ff @(posedge clk, negedge rst_)
        if (!rst_) begin
            {wr_ptr, rd_ptr, cnt} <= 0;
            FIFO <= '{default:0};
        end else begin: rw_data
            //read and write simultaneously in the same position is not allowed 
            if (fifo_write && fifo_read && wr_ptr==rd_ptr) disable rw_data; 

            if (fifo_write && !fifo_full) begin
                FIFO[wr_ptr] <= fifo_data_in;
                wr_ptr <= (wr_ptr>=DEPTH-1) ? 1'b0 : wr_ptr + 1'b1;
                //in case of simultanious read and write cnt = cnt +1-1 = cnt
                if (!(fifo_write && fifo_read)) cnt <= cnt + 1;
            end
        
            if (fifo_read && !fifo_empty) begin
                fifo_data_out <= FIFO[rd_ptr];
                rd_ptr <= (rd_ptr>=DEPTH-1) ? 1'b0 : rd_ptr + 1'b1;
                //in case of simultanious read and write cnt = cnt +1-1 = cnt
                if (!(fifo_write && fifo_read)) cnt <= cnt - 1;
            end
        end

    assign fifo_full = (cnt>=DEPTH) ? 1'b1 : 1'b0; 
    assign fifo_empty = (cnt==0) ? 1'b1 : 1'b0; 

endmodule

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
            if (wr_ptr!=rd_ptr) 
               ##1  wr_ptr==$past(wr_ptr)+1'b1 && rd_ptr==$past(rd_ptr)+1'b1 && cnt==$past(cnt)
            else //read && write in same position not allowed
                ##1 wr_ptr==$past(wr_ptr) && rd_ptr==$past(rd_ptr) && cnt==$past(cnt);
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

module fifo_tbench;
logic clk, rst_, fifo_write, fifo_read;
logic fifo_full, fifo_empty;
logic [15:0] fifo_data_in=16'b1;
logic [15:0] fifo_data_out;

fifo U1(.*);
bind U1 fifo_prop fifo_bind (.*,.wr_ptr(U1.wr_ptr),.rd_ptr(U1.rd_ptr),.cnt(U1.cnt));

initial begin
    clk=0;
    forever #2 clk = ~clk;
    
end
always @(negedge clk) fifo_data_in <= fifo_data_in + 1'b1;

always begin
    repeat(2) @(posedge clk);
    {fifo_read, fifo_write} <= 2'b0; rst_ <= 1;
    @(posedge clk) rst_ <= 0;
    @(posedge clk) rst_ <= 1;
    repeat(2) @(posedge clk);
    @(negedge clk) fifo_write <= 1'b1;
    @(negedge clk) fifo_write <= 1'b1;fifo_read <= 1'b1;
    @(negedge clk) fifo_write <= 1'b1;fifo_read <= 1'b1;
    @(negedge clk) fifo_write <= 1'b0;fifo_read <= 1'b1;
    @(negedge clk) fifo_write <= 1'b1;fifo_read <= 1'b1;
    @(negedge clk) fifo_write <= 1'b0;fifo_read <= 1'b0;
    fifo_data_in <= $urandom(1);
    @(negedge clk) fifo_write <= 1'b1;
    repeat(16) @(posedge clk);
    @(negedge clk) fifo_write <= 1'b1;
    @(negedge clk) fifo_write <= 1'b0;fifo_read <= 1'b1;
    @(negedge clk) fifo_read <= 1'b1;
     repeat(16) @(posedge clk);
    @(negedge clk) fifo_read <= 1'b0;
    @(negedge clk) rst_ <= 0;
    @(negedge clk) fifo_read <= 1'b1;
    @(negedge clk) fifo_read <= 1'b0;
end
endmodule