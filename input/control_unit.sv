`include "audioport.svh"

import audioport_pkg::*;

module control_unit
  
  (input logic clk,
   input logic 			     rst_n,

   input logic 			     psel_in,
   input logic 			     penable_in,
   input logic 			     pwrite_in,
   input logic [31:0] 		     paddr_in,
   input logic [31:0] 		     pwdata_in,
   output logic [31:0] 		     prdata_out,
   output logic 		     pready_out,
   output logic 		     pslverr_out,
   
   output logic [1:0][23:0] 	     abuf_out,
   output logic 		     tick_out,
   output logic 		     irq_out,

   output logic 		     cfg_out,
   output logic [31:0] 		     cfg_reg_out,
   output logic 		     level_out,
   output logic [31:0] 		     level_reg_out,
   output logic [DSP_REGISTERS-1:0][31:0] dsp_regs_out,
   output logic 		     clr_out,

   output logic 		     play_out,
   input logic 			     req_in
   );
   
   logic 			     ready;
   logic [INT_ADDR_BITS-1:0] 	     int_addr;
   logic 			     write;
   logic [$clog2(CMD_WAIT_STATES):0] wait_counter_r;
   logic 			       start;
   logic 			       stop;
   logic 			       clr;
   logic [AUDIOPORT_REGISTERS-1:0][31:0] rbank_r;   

   always_ff @(posedge clk or negedge rst_n)
     begin : wait_counter
	if (rst_n == '0)
	  wait_counter_r <= '0;
	else
	  begin
	     if (wait_counter_r == 0)
	       begin
		  if (psel_in && !penable_in && pwrite_in && int_addr == CMD_REG_INT_ADDRESS)	  
		    wait_counter_r <= 1;
	       end
	     else if (wait_counter_r < CMD_WAIT_STATES)
	       begin
		  wait_counter_r <= wait_counter_r + 1;
	       end
	     else
	       wait_counter_r <= 0;
	  end
     end : wait_counter
   
   always_comb
     begin : ready_decoder
	if (wait_counter_r == 0)
	  ready = '1;
	else
	  ready = '0;
     end : ready_decoder

   
endmodule
