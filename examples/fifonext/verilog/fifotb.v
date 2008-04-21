`include "fifostack.v"
`include "fifoqueue.v"
module fifostacktb ();

reg clock;
reg reset;
reg [31:0] data_in;
reg enqueue; 
reg dequeue; 

wire empty_stack; 
wire full_stack;
wire [31:0] data_out_stack;

wire empty_queue; 
wire full_queue;
wire [31:0] data_out_queue;

fifostack fifostack_inst (
  clock,
  reset,
  enqueue,
  dequeue,
  data_in,
  empty_stack,
  full_stack,
  data_out_stack
);

fifoqueue fifoqueue_inst (
  clock,
  reset,
  enqueue,
  dequeue,
  data_in,
  empty_queue,
  full_queue,
  data_out_queue
);


initial begin
  $display ("");
  $display ("c = clock, r = reset, e = enqueue, d = dequeue, es = empty_stack, eq = empty_queue, fs = full_stack, fq = full_queue");
  $display ("");
  $display ("c r e d es eq fs fq data_in                          data_out_stack                   data_out_queue                   time");
  $monitor ("%b %b %b %b %b  %b  %b  %b  %b %b %b %g", clock, reset, enqueue, dequeue, empty_stack, empty_queue, full_stack, full_queue, data_in, data_out_stack, data_out_queue, $time);
  clock = 1;
  reset = 0;
  enqueue = 0;
  dequeue = 0;
  #10 reset = 1;
  #10 data_in = 32'b00000000000000000000000000000000;
      enqueue = 1;
  #10 data_in = 32'b00000000000000000000000000000001;
  #10 data_in = 32'b00000000000000000000000000000010;
  #10 data_in = 32'b00000000000000000000000000000011;
  #10 data_in = 32'b00000000000000000000000000000100;
  #10 data_in = 32'b00000000000000000000000000000101;
  #10 data_in = 32'b00000000000000000000000000000110;
  #10 data_in = 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx;
      enqueue = 0;
      dequeue = 1;
  #10;
  #10;
  #10;
  #10;
  #10;
  #10;
  #10 $finish;
end

always begin
  #5 clock = ~clock;
end


endmodule
