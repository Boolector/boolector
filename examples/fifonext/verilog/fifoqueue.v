module fifoqueue (
    clock,
    reset,
    enqueue,
    dequeue,
    data_in,
    empty,
    full,
    data_out
);

input clock;
input reset;
input enqueue;
input dequeue;
input [31:0] data_in;

output empty;
output full;
output [31:0] data_out;

wire clock;
wire reset; /* active low */
wire enqueue;
wire dequeue;
wire [31:0] data_in;

reg [2:0] head; /* address of first element */
reg [2:0] tail; /* address of next free slot */
reg [31:0] mem [0:7]; /* internal memory */

reg [31:0] data_out;

reg empty;
reg full;

always @ (posedge clock)
begin : fifoqueue
  if (reset == 1'b0) begin
    head <= # 1 3'b000;
    tail <= # 1 3'b000;
    empty <= # 1 1'b1;
    full <= # 1 1'b0;
  end
  /* if enqueue and dequeue are both 1 or both 0, we
   * do nothing */
  else if ((enqueue ^ dequeue) == 1'b1) begin
    if (enqueue == 1'b1) begin
      empty <= # 1 1'b0;
      if (full == 1'b0) begin
        mem[tail] <= # 1 data_in;
        tail <= # 1 tail + 3'b001;
      end
      /* we do not use the last slot */
      if (tail + 3'b010 == head) begin
        full <= # 1 1'b1;
      end
    end
    /* dequeue is 1 */
    else begin
      if (empty == 1'b0) begin
        data_out <= # 1 mem[head];
        head <= # 1 head + 3'b001;
      end
      if (head + 3'b001 == tail) begin
        empty <= # 1 1'b1;
      end
      full <= # 1 1'b0;
    end
  end
end

endmodule
