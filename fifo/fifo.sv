module fifo #(parameter WIDTH = 16, parameter DEPTH = 16) (
    input   logic clk, rst_, fifo_write, fifo_read, 
    output  logic fifo_full, fifo_empty,
    input   logic [WIDTH-1:0] fifo_data_in,
    output  logic [WIDTH-1:0] fifo_data_out
);

    logic [$clog2(DEPTH)-1:0] wr_ptr, rd_ptr;
    logic [$clog2(DEPTH):0] cnt;
    logic [WIDTH-1:0] FIFO [DEPTH];

    always_ff @(posedge clk, negedge rst_)
        if (!rst_) begin
            {wr_ptr, rd_ptr, cnt} <= 0;
            FIFO <= '{default:0};
        end else begin: rw_data

            if (fifo_write && !fifo_full) begin
                FIFO[wr_ptr] <= fifo_data_in;
                wr_ptr <= (wr_ptr>=DEPTH-1) ? 1'b0 : wr_ptr + 1'b1;
                //in case of simultanious (and legal) read and write: cnt = cnt +1-1 = cnt
                if (!(fifo_read && !fifo_empty)) cnt <= cnt + 1;
            end
        
            if (fifo_read && !fifo_empty) begin
                fifo_data_out <= FIFO[rd_ptr];
                rd_ptr <= (rd_ptr>=DEPTH-1) ? 1'b0 : rd_ptr + 1'b1;
                //in case of simultanious (and legal) read and write: cnt = cnt +1-1 = cnt
                if (!(fifo_write && !fifo_full)) cnt <= cnt - 1;
            end
        end

    assign fifo_full = (cnt>=DEPTH) ? 1'b1 : 1'b0; 
    assign fifo_empty = (cnt==0) ? 1'b1 : 1'b0; 

endmodule
