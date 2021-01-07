`ifndef SYNTHESIS

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module cdc_unit_tb   #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic clk ='0;
   logic rst_n = '0;
   logic [1:0][23:0] dsp_in;
   logic 	     play_in;
   logic 	     tick_in;
   logic 	     cfg_in;
   logic [31:0]      cfg_reg_in;
   logic 	     req_out;
   
   logic 	     mclk ='0;
   logic 	     mrst_n;
   logic [1:0][23:0] dsp_out;
   logic 	     play_out;
   logic 	     tick_out;
   logic 	     cfg_out;
   logic [31:0]      cfg_reg_out;
   logic 	     req_in;
   
   logic [1:0][23:0] ref_dsp_out;
   logic 	     ref_play_out;
   logic 	     ref_tick_out;
   logic 	     ref_cfg_out;
   logic [31:0]      ref_cfg_reg_out;
   logic 	     ref_req_out;

   ////////////////////////////////////////////////////////////////////////////
   //
   // Clock, reset generation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	realtime delay;
	int counter;
	counter = 0;
	clk = '0;
	forever
	  begin 
	     #(CLK_PERIOD/2) clk = ~clk;
	     ++counter;
	     if (counter == 101)
	       begin
		  // Insert random delay to make clk and mclk start out of synch		  
		  delay = real'($urandom_range(0, CLK_PERIOD/2))/23.0;
		  #(delay);
		  counter = 0;
	       end
	  end
     end
   
   initial
     begin
	realtime delay;
	mclk = '0;
	// Insert random delay to make clk and mclk start out of synch
	delay = real'($urandom_range(0, MCLK_PERIOD/2))/11.0;
	#(delay);
	forever begin
	   #(MCLK_PERIOD/2) mclk = ~mclk;
	end
     end

   initial
     begin
	rst_n = '0;
	@(negedge clk) rst_n = '0;
	@(negedge clk) rst_n = '1;	
     end

      initial
     begin
	mrst_n = '0;
	@(negedge mclk) mrst_n = '0;
	@(negedge mclk) mrst_n = '1;	
     end

   ////////////////////////////////////////////////////////////////////////////
   //
   // Instantiation of DUT and test program
   //
   ////////////////////////////////////////////////////////////////////////////
   
   cdc_unit DUT_INSTANCE (.*);
   cdc_unit_test TEST (.*);

   ////////////////////////////////////////////////////////////////////////////
   //
   // Include SVA assertion module bindings only in RTL simulation
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

	    cdc_unit REF_INSTANCE
	      (.clk(clk),
	       .rst_n(rst_n),
	       .dsp_out(ref_dsp_out),
	       .cfg_out(ref_cfg_out),
	       .play_out(ref_play_out),
	       .tick_out(ref_tick_out),
	       .cfg_reg_out(ref_cfg_reg_out),
	       .req_out(ref_req_out),
	       .*
	       );

	 
	 //////////////////////////////////////
         // Comparison code begin
	 //////////////////////////////////////
	 
	 always @(posedge mclk)
	   begin
	      if (rst_n == '1)
		begin
		   assert(dsp_out == ref_dsp_out) else $error("DUT != REF: dsp_out");
		   assert(cfg_out == ref_cfg_out) else $error("DUT != REF: cfg_out");
		   assert(cfg_reg_out == ref_cfg_reg_out) else $error("DUT != REF: cfg_reg_out");
		   assert(tick_out == ref_tick_out) else $error("DUT != REF: tick_out");
		   assert(play_out == ref_play_out) else $error("DUT != REF: play_out");
		end
	   end

	 always @(posedge clk)
	   begin
	      if (rst_n == '1)
		begin
		   assert(req_out == ref_req_out) else $error("DUT != REF: req_out");		   
		end
	   end
	 
	 //////////////////////////////////////
	 // Comparison code end
	 //////////////////////////////////////
	 
      end 

      
   endgenerate

   initial
     begin
	save_test_parameters("reports/3_vsim_cdc_unit_test_parameters.txt");	
     end
   
endmodule // cdc_unit_tb


`endif
