module fifo_tbench;
logic clk, rst_, fifo_write, fifo_read;
logic fifo_full, fifo_empty;
logic [15:0] fifo_data_in;
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
    @(negedge clk) fifo_write <= 1'b1; fifo_data_in<=1;
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
