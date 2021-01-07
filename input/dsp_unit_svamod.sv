`include "audioport.svh"

`ifndef SYNTHESIS

import audioport_pkg::*;

module dsp_unit_svamod(
		       input logic 			clk,
		       input logic 			rst_n,
		       input logic 			tick_in,
		       input logic 			cfg_in,
		       input logic 			level_in,
		       input logic 			clr_in, 
		       input logic [1:0][23:0] 		abuf_in,
		       input logic [DSP_REGISTERS-1:0][31:0] dsp_regs_in,
		       input logic [31:0] 		level_reg_in,
		       input logic [31:0] 		cfg_reg_in,
		       input logic [1:0][23:0] 		dsp_out,
		       input logic 			valid_out			       
		       );


   // ---------------------------------------------------------------------------      
   // Check for unknown 'x states (see xcheck macro definitions in audioport.svh)
   // ---------------------------------------------------------------------------      
   
   `xcheck(tick_in);
   `xcheck(cfg_in);
   `xcheck(level_in);
   `xcheck(clr_in);
   `xcheck(abuf_in);
   `xcheck(dsp_regs_in);
   `xcheck(level_reg_in);
   `xcheck(cfg_reg_in);      
   `xcheck(dsp_out);
   `xcheck(valid_out);         

   //////////////////////////////////////////////////////////////////////////////
   //
   // 1. Assumptions for formal verification
   //
   //////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_dsp_unit

   property f_cmd_mutex;
      @(posedge clk) disable iff (rst_n == '0)
	$onehot0({cfg_in, level_in, clr_in});
   endproperty
   
   mf_cmd_mutex: assume property(f_cmd_mutex)
     else $error("More than one command inputs high");

   // ---------------------------------------------------------------------------   
   // f-tickin: tick_in_pulse
   // ---------------------------------------------------------------------------

   property f_tick_in_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(tick_in) |=> $fell(tick_in) ##1 !tick_in [* DSP_UNIT_MAX_LATENCY];
   endproperty

   mf_tick_in_pulse: assume property ( f_tick_in_pulse )
     else $error("tick_in length > 1 cycles.");   
   
   // ---------------------------------------------------------------------------   
   // f-cfgin: cfg_in_pulse
   // ---------------------------------------------------------------------------

   property f_cfg_in_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(cfg_in) |=> $fell(cfg_in);
   endproperty

   mf_cfg_in_pulse: assume property (f_cfg_in_pulse)
     else $error("cfg_in length > 1 cycles.");   

   // ---------------------------------------------------------------------------   
   // f-clrin: clr_in_pulse
   // ---------------------------------------------------------------------------

   property f_clr_in_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(clr_in) |=> $fell(clr_in);
   endproperty

   mf_clr_in_pulse: assume property (f_clr_in_pulse)
     else $error("clr_in length > 1 cycles.");   

   // ---------------------------------------------------------------------------   
   // f-levelin: level_in_pulse
   // ---------------------------------------------------------------------------

   property f_level_in_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(level_in) |=> $fell(level_in);
   endproperty

   mf_level_in_pulse: assume property (f_level_in_pulse)
     else $error("level_in length > 1 cycles.");   
   
`endif

   //////////////////////////////////////////////////////////////////////////////
   //
   // Blackbox Assertions
   //
   //////////////////////////////////////////////////////////////////////////////   

   // ---------------------------------------------------------------------------   
   // f-valid-pulse: f_valid_out_pulse
   // ---------------------------------------------------------------------------

   property f_valid_out_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(valid_out) |=> $fell(valid_out);
   endproperty

   af_valid_out_pulse: assert property (f_valid_out_pulse)
     else $error("valid_out length > 1 cycles.");   

   // ---------------------------------------------------------------------------   
   // f-max-latency: f_max_latency
   // ---------------------------------------------------------------------------
   
   property f_max_latency;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(tick_in) |=> !valid_out [* 1:DSP_UNIT_MAX_LATENCY-1] ##1 valid_out;
   endproperty

   af_max_latency: assert property (f_max_latency)
     else $error("dsp_unit max. latency exceeded");   
   cf_max_latency: cover property (f_max_latency);

   // ---------------------------------------------------------------------------   
   // f-monomode: f_monomode
   // ---------------------------------------------------------------------------
   
   property f_monomode;
      @(posedge clk) disable iff (rst_n == '0)
	($rose(cfg_in) && (cfg_reg_in[CFG_MONO] == MODE_MONO)) ##1 (!cfg_in throughout tick_in [-> 1]) |=> 
					 !valid_out [* 1:DSP_UNIT_MAX_LATENCY-1] ##1 (valid_out && (dsp_out[0] == dsp_out[1]));
   endproperty

   af_monomode: assert property (f_monomode)
     else $error("Left and right outputs different in mono mode");
   cf_monomode: cover property (f_monomode);
   
   //////////////////////////////////////////////////////////////////////////////
   //
   // Covergroups
   //
   //////////////////////////////////////////////////////////////////////////////
   
   // ---------------------------------------------------------------------------      
   // cg_dsp_modes
   // ---------------------------------------------------------------------------      
      
   covergroup cg_dsp_modes @(posedge clk iff (cfg_in));
    coverpoint cfg_reg_in[3:0]
      { 
       bins modes[] = { 4'b0000, 4'b0001, 4'b0010, 
			4'b0100, 4'b0101, 4'b0110,
			4'b1000, 4'b1001, 4'b1010, 			 
			4'b1100, 4'b1101, 4'b1110 };			 
    }
   endgroup
   cg_dsp_modes cg_dsp_modes_inst = new;   
   
endmodule

`endif //  `ifndef SYNTHESIS
