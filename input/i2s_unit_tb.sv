`ifndef SYNTHESIS

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module i2s_unit_tb #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic 	   clk;
   logic 	   rst_n;
   logic 	   play_in;
   logic 	   tick_in;   
   logic [23:0]    audio_in_0;
   logic [23:0]    audio_in_1;   
   logic 	   cfg_in;
   logic [31:0]    cfg_reg_in;
   logic 	   req_out;
   logic  ws_out;
   logic  sck_out;
   logic  sdo_out;

   logic  ref_ws_out;
   logic  ref_sck_out;
   logic  ref_sdo_out;

   i2s_if i2s(clk, rst_n);
   assign i2s.sdo = sdo_out;
   assign i2s.sck = sck_out;
   assign i2s.ws  = ws_out;
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Clock, reset generation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	clk = '0;
	forever #(MCLK_PERIOD/2) clk = ~clk;
     end
   
   initial
     begin
	rst_n = '0;
	@(negedge clk) rst_n = '0;
	@(negedge clk) rst_n = '1;	
     end

   ////////////////////////////////////////////////////////////////////////////
   //
   // Instantiation of DUT and test program
   //
   ////////////////////////////////////////////////////////////////////////////
   
   i2s_unit DUT_INSTANCE (.*);
   i2s_unit_test TEST (.*);

   ////////////////////////////////////////////////////////////////////////////
   //
   // Include SVA assertion module bindings
   //
   ////////////////////////////////////////////////////////////////////////////

`include "sva_bindings.svh"
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Reference model instantiation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL

	    i2s_unit REF_INSTANCE
	      (.sck_out(ref_sck_out),
	       .ws_out(ref_ws_out),
	       .sdo_out(ref_sdo_out),
	       .*
	       );

	 
	 //////////////////////////////////////
         // Comparison code begin
	 //////////////////////////////////////
	 
	 always @(posedge clk)
	   begin
	      if (rst_n == '1)
		begin
		   assert(sdo_out == ref_sdo_out) else $error("DUT != REF: sdo_out");
		   assert(sck_out == ref_sck_out) else $error("DUT != REF: sck_out");
		   assert(ws_out == ref_ws_out) else $error("DUT != REF: ws_out");
		end
	   end
	 
	 //////////////////////////////////////
	 // Comparison code end
	 //////////////////////////////////////
	 
      end 

      
   endgenerate

   initial
     begin
	save_test_parameters("reports/3_vsim_i2s_unit_test_parameters.txt");	
     end
   
endmodule 


`endif
