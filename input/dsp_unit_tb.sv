
`ifndef SYNTHESIS

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module dsp_unit_tb  #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic clk;
   logic rst_n;
   logic tick_in;
   logic cfg_in;
   logic level_in;
   logic clr_in;		
   logic [1:0][23:0] abuf_in;
   logic [DSP_REGISTERS-1:0][31:0] dsp_regs_in;
   logic [31:0] 		     level_reg_in;
   logic [31:0] 		     cfg_reg_in;
   logic [1:0][23:0] 		     dsp_out;
   logic [1:0][23:0] 		     ref_dsp_out;

   ////////////////////////////////////////////////////////////////////////////
   //
   // Clock, reset generation
   //
   ////////////////////////////////////////////////////////////////////////////

   initial
     begin
	clk = '0;
	forever #(CLK_PERIOD) clk = ~clk;
     end
   
   initial
     begin
	rst_n = '0;
	@(negedge clk);
	@(negedge clk) rst_n = '1;	
     end

   ////////////////////////////////////////////////////////////////////////////
   //
   // Instantiation of DUT and test program
   //
   ////////////////////////////////////////////////////////////////////////////
   
   dsp_unit DUT_INSTANCE (.*);
   dsp_unit_test TEST (.*);
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Include SVA assertion module bindings
   //
   ////////////////////////////////////////////////////////////////////////////

 `include "sva_bindings.svh"
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Reference model
   //
   ////////////////////////////////////////////////////////////////////////////
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 
	 dsp_unit REF_INSTANCE (.dsp_out(ref_dsp_out),
				      .*);	 
      end

	 //////////////////////////////////////
         // Comparison code begin
	 //////////////////////////////////////
	 
	 always @(posedge clk or negedge rst_n)
	   begin
	      if (rst_n == '1)
		begin
		end
	   end
	 
	 //////////////////////////////////////
	 // Comparison code end
	 //////////////////////////////////////
      
   endgenerate

   
endmodule


`endif
