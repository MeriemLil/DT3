`ifndef SYNTHESIS

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module control_unit_tb  #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic clk;
   logic rst_n;

   // Signals connect to DUT ports

   logic  psel_in;
   logic  penable_in;
   logic  pwrite_in;
   logic [31:0]  paddr_in;
   logic [31:0] pwdata_in;
   logic [31:0] prdata_out;
   logic pready_out;
   logic pslverr_out;

   logic [1:0][23:0] abuf_out;   
   logic irq_out;
   logic cfg_out;
   logic level_out;
   logic clr_out;   
   logic [31:0] cfg_reg_out;
   logic [31:0] level_reg_out;
   logic [DSP_REGISTERS-1:0][31:0] dsp_regs_out;
   logic tick_out;
   logic req_in;
   
   // Signals for reference model outputs
   
   logic [31:0] ref_prdata_out;
   logic 	ref_pready_out;
   logic 	ref_pslverr_out;
   logic [1:0][23:0] ref_abuf_out;   
   logic ref_irq_out;
   logic ref_cfg_out;
   logic ref_level_out;
   logic ref_clr_out;   
   logic [31:0] ref_cfg_reg_out;
   logic [31:0] ref_level_reg_out;
   logic [DSP_REGISTERS-1:0][31:0] ref_dsp_regs_out;
   logic ref_tick_out;
   logic ref_req_in;
   

   ////////////////////////////////////////////////////////////////////////////
   //
   // Interface object declarations and connections
   //
   ////////////////////////////////////////////////////////////////////////////
   
   apb_if apb(clk, rst_n);   
   irq_out_if irq(clk, rst_n);   

   assign psel_in = apb.psel;
   assign penable_in = apb.penable;   
   assign pwrite_in = apb.pwrite;
   assign paddr_in = apb.paddr;
   assign pwdata_in = apb.pwdata;
   assign apb.prdata = prdata_out;
   assign apb.pready = pready_out;
   assign apb.pslverr = pslverr_out;

   assign irq.irq_out = irq_out;   

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
   // DUT instantiation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   control_unit DUT_INSTANCE
     (.clk(clk),
      .rst_n(rst_n),
      .psel_in(psel_in),
      .penable_in(penable_in),
      .pwrite_in(pwrite_in),
      .paddr_in(paddr_in),	      
      .pwdata_in(pwdata_in),
      .prdata_out(prdata_out),
      .pready_out(pready_out),
      .pslverr_out(pslverr_out),
      .clr_out(clr_out),   
      .cfg_out(cfg_out),
      .cfg_reg_out(cfg_reg_out),
      .level_out(level_out),
      .level_reg_out(level_reg_out),
      .dsp_regs_out(dsp_regs_out),
      .abuf_out(abuf_out),
      .irq_out(irq_out),
      .tick_out(tick_out),
      .play_out(play_out),      
      .req_in(req_in)
      );

   ////////////////////////////////////////////////////////////////////////////
   //
   // Include SVA assertion module bindings only in RTL simulation
   //
   ////////////////////////////////////////////////////////////////////////////

 `include "sva_bindings.svh"
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Test program instantiation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   control_unit_test TEST (.clk(clk),
			   .rst_n(rst_n),
			   .apb(apb),
			   .irq(irq),			   
			   .cfg_out(cfg_out),
			   .cfg_reg_out(cfg_reg_out),
			   .level_out(level_out),
			   .level_reg_out(level_reg_out),
			   .dsp_regs_out(dsp_regs_out),
			   .clr_out(clr_out),
			   .abuf_out(abuf_out),
			   .tick_out(tick_out),
			   .req_in(req_in)
			   );
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Reference model instantiation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL

	    control_unit REF_INSTANCE
	      (.clk(clk),
	       .rst_n(rst_n),
	       .prdata_out(ref_prdata_out),
	       .pready_out(ref_pready_out),
	       .pslverr_out(ref_pslverr_out),
	       .irq_out(ref_irq_out),
	       .cfg_out(ref_cfg_out),
	       .cfg_reg_out(ref_cfg_reg_out),
	       .level_out(ref_level_out),
	       .level_reg_out(ref_level_reg_out),
	       .dsp_regs_out(ref_dsp_regs_out),
	       .clr_out(ref_clr_out),
	       .abuf_out(ref_abuf_out),	       
	       .tick_out(ref_tick_out),
	       .req_in(ref_req_in),	       
	       .*
	       );

	 
	 //////////////////////////////////////
         // Comparison code begin
	 //////////////////////////////////////
	 
	 always @(posedge clk or negedge rst_n)
	   begin
	      if (rst_n == '1)
		begin
		   assert(prdata_out == ref_prdata_out) else $error("DUT != REF: prdata");
		   assert(pready_out == ref_pready_out) else $error("DUT != REF: pready");		   		   
		   assert(irq_out == ref_irq_out) else $error("DUT != REF: irq_out");
		   assert(cfg_reg_out == ref_cfg_reg_out) else $error("DUT != REF: cfg_reg_out");
		   assert(cfg_out == ref_cfg_out) else $error("DUT != REF: cfg_out");
		   assert(level_reg_out == ref_level_reg_out) else $error("DUT != REF: level_reg_out");
		   assert(level_out == ref_level_out) else $error("DUT != REF: level_out");
		   assert(dsp_regs_out == ref_dsp_regs_out) else $error("DUT != REF: eq_coeffs_out");
		   assert(clr_out == ref_clr_out) else $error("DUT != REF: clr_out");   
		   assert(tick_out == ref_tick_out) else $error("DUT != REF: tick_out");
		end
	   end
	 
	 //////////////////////////////////////
	 // Comparison code end
	 //////////////////////////////////////
	 
      end 

      
   endgenerate

   initial
     begin
	save_test_parameters("reports/3_vsim_control_unit_test_parameters.txt");	
     end
   
endmodule 



`endif
