module fifo #(parameter WIDTH = 16, parameter DEPTH = 16) (
    input   logic clk, rst_, fifo_write, fifo_read, 
    output  logic fifo_full, fifo_empty,
    input   logic [WIDTH-1:0] fifo_data_in,
    output  logic [WIDTH-1:0] fifo_data_out
);

    integer wr_ptr, rd_ptr, cnt;
    logic [WIDTH-1:0] FIFO [DEPTH];

    always_ff @(posedge clk, negedge rst_) begin
        if (!rst_) begin
            {wr_ptr, rd_ptr, cnt} <= 0;
            FIFO <= '{default:0};
        end else begin
            unique case (1'b1)
                fifo_write: 
                    if (!fifo_full) begin
                        FIFO[wr_ptr] <= fifo_data_in;
                        wr_ptr <= (wr_ptr>=DEPTH-1) ? 0 : wr_ptr + 1;
                        cnt <= cnt + 1;
                    end
                fifo_read:
                    if (!fifo_empty) begin
                        fifo_data_out <= FIFO[rd_ptr];
                        rd_ptr <= (rd_ptr>=DEPTH-1) ? 0 : rd_ptr + 1;
                        cnt <= cnt - 1;
                    end
                default: ;
            endcase
        end
    end

    assign fifo_full = (cnt>=DEPTH) ? 1'b1 : 1'b0; 
    assign fifo_empty = (cnt==0) ? 1'b1 : 1'b0; 

endmodule

module fifo_tbench;
logic clk, rst_, fifo_write, fifo_read;
logic fifo_full, fifo_empty;
logic [15:0] fifo_data_in;
logic [15:0] fifo_data_out;

fifo U1(.*);

initial begin
    clk=0;
    forever begin
        #2 clk = ~clk;
    end
end

always begin
    repeat(4) @(posedge clk);
    fifo_data_in <= $urandom;
    {fifo_read, fifo_full} <= 2'b0;
    @(posedge clk) rst_ <= 1;
    @(posedge clk) rst_ <= 0;
    @(posedge clk) rst_ <= 0;
    @(posedge clk) rst_ <= 1;
    repeat(4) @(posedge clk);
    @(posedge clk) fifo_write <= 1'b1;
    @(posedge clk) fifo_write <= 1'b1;
    @(posedge clk) fifo_write <= 1'b0;
    fifo_data_in <= $urandom(1);
    @(posedge clk) fifo_write <= 1'b1;
    @(posedge clk) fifo_write <= 1'b1;
    @(posedge clk) fifo_write <= 1'b1;
    @(posedge clk) fifo_write <= 1'b0;
    repeat(4) @(posedge clk);
    @(posedge clk) fifo_read <= 1'b1;
    @(posedge clk) fifo_read <= 1'b1;
    @(posedge clk) fifo_read <= 1'b1;
    @(posedge clk) fifo_read <= 1'b0;
    @(negedge clk) rst_ <= 0;
    @(posedge clk) fifo_read <= 1'b1;
    @(posedge clk) fifo_read <= 1'b0;
end
endmodule