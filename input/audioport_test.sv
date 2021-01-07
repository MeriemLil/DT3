`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program audioport_test
  
  (input logic clk,
   input logic 	rst_n,
   input logic 	mclk,
   input logic 	mrst_n, 
		apb_if apb,
		irq_out_if irq,
		i2s_if i2s, 
   output logic test_mode_sel,
   input logic 	sck_out,
   input logic 	ws_out,
   input logic 	sdo_out
   );

   initial
     begin : test_program
	logic         fail;
	logic [31:0]  addr;
	logic [31:0]  wdata;

	test_mode_sel = '0;
	apb.reset;
	#1us;

	addr = CMD_REG_APB_ADDRESS;
	wdata = { CMD_START, 24'h000000 };
	apb.write(addr, wdata, fail);	 	

	#100us;

	addr = CMD_REG_APB_ADDRESS;
	wdata = { CMD_STOP, 24'h000000 };
	apb.write(addr, wdata, fail);	     

	#1us;

     end : test_program

endprogram
     
