`include "audioport.svh"

`ifndef SYNTHESIS

import audioport_pkg::*;


module cdc_unit_svamod(
		input logic 		clk,
		input logic 		rst_n,
		input logic [1:0][23:0] dsp_in,
		input logic 		tick_in,
		input logic 		cfg_in,
		input logic [31:0] 	cfg_reg_in,
		input logic 		play_in,
		input logic 		req_out,
		       
		input logic 		mclk,
		input logic 		mrst_n,
		input logic [1:0][23:0] dsp_out,
		input logic 		tick_out,
		input logic 		cfg_out,
		input logic [31:0] 	cfg_reg_out,
		input logic 		play_out,
		input logic 		req_in
		);

   // ---------------------------------------------------------------------------      
   // Check for unknown 'x states (see xcheck macro definitions in audioport.svh)
   // ---------------------------------------------------------------------------      
   
   `xcheck(dsp_in);
   `xcheck(tick_in);
   `xcheck(cfg_in);
   `xcheck(cfg_reg_in);
   `xcheck(play_in);
   `xcheck(req_out);
   `xcheck(dsp_out);
   `xcheck(tick_out);
   `xcheck(cfg_out);
   `xcheck(play_out);
   `xcheck(cfg_reg_out);
   `xcheck(req_in);

   //////////////////////////////////////////////////////////////////////////////
   //
   // 1. Assumptions for formal verification
   //
   //////////////////////////////////////////////////////////////////////////////

 `ifdef design_top_is_cdc_unit

   // ---------------------------------------------------------------------------      
   // f-audiosync: f_tick_pulse
   // ---------------------------------------------------------------------------      

   property f_tick_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(tick_in) |=> !tick_in;
   endproperty
   
   mf_tick_pulse: assume property(f_tick_pulse)
     else $error("tick_in pulse width was not one clock cycle");

   // ---------------------------------------------------------------------------      
   // f-audiosync: f_tick_interval
   // ---------------------------------------------------------------------------      

   property f_tick_interval;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(tick_in) |=> $fell(tick_in) ##1 !tick_in [* CDC_HANDSHAKER_INTERVAL-2];
   endproperty
   
   mf_tick_interval: assume property(f_tick_interval)
     else $error("tick_in interval too short");
      

   // ---------------------------------------------------------------------------      
   // f-cfg: f_cfg_pulse
   // ---------------------------------------------------------------------------      

   property f_cfg_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(cfg_in) |=> !cfg_in;
   endproperty
   
   mf_cfg_pulse: assume property(f_cfg_pulse)
     else $error("cfg_in pulse width was not one clock cycle");

   // ---------------------------------------------------------------------------      
   // f-cfgsync: f_cfg_interval
   // ---------------------------------------------------------------------------      

   property f_cfg_interval;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(cfg_in) |=> $fell(cfg_in) ##1 !cfg_in [* CDC_HANDSHAKER_INTERVAL-2];
   endproperty
   
   mf_cfg_interval: assume property(f_cfg_interval)
     else $error("cfg_in interval too short");

   // ---------------------------------------------------------------------------      
   // f-playsync: f_playlength
   // ---------------------------------------------------------------------------      

   property f_playlength;
      @(posedge clk) disable iff (rst_n == '0)      
       !$stable(play_in) |=>  $stable(play_in) [* CDC_BITSYNC_INTERVAL-1];
   endproperty
   
   mf_playlength: assume property(f_playlength)
     else $error("play_in not stable long enough.");
   
   // ---------------------------------------------------------------------------      
   // f-reqsync: f_req_pulse
   // ---------------------------------------------------------------------------      

   property f_req_pulse;
      @(posedge mclk) disable iff (mrst_n == '0)
	$rose(req_in) |=> !req_in;
   endproperty
   
   mf_req_pulse: assume property(f_req_pulse)
     else $error("req_in pulse width was not one clock cycle");

`endif
   
   //////////////////////////////////////////////////////////////////////////////
   //
   // 2. Blackbox Assertions
   //
   //////////////////////////////////////////////////////////////////////////////

   // ---------------------------------------------------------------------------      
   // f-audiosync: f_audiosync
   // ---------------------------------------------------------------------------
   
   property f_audio_sync;
      logic [1:0][23:0] txdata;
      disable iff (rst_n == '0 || mrst_n == '0)       
	@(posedge clk) ($rose(tick_in), txdata = dsp_in) |=> @(posedge mclk) (!tick_out [* 0:CDC_HANDSHAKER_LATENCY]) ##1  tick_out && (txdata == dsp_out) ##1 !tick_out;
      
   endproperty

   af_audio_sync: assert property ( f_audio_sync )
     else $error("tick_out/dsp_out sync failure.");
   cf_audio_sync: cover property ( f_audio_sync );
   
   // ---------------------------------------------------------------------------      
   // f-cfgsync: f_cfgsync
   // ---------------------------------------------------------------------------
   
   property f_cfg_sync;
      logic [31:0] txdata;
      disable iff (rst_n == '0 || mrst_n == '0)       
	@(posedge clk) ($rose(cfg_in), txdata = cfg_reg_in) |=> @(posedge mclk) (!cfg_out [* 0:CDC_HANDSHAKER_LATENCY]) ##1  cfg_out && (txdata == cfg_reg_out) ##1 !cfg_out;
   endproperty

   af_cfg_sync: assert property ( f_cfg_sync )
     else $error("cfg_out/cfg_reg_out failure");
   cf_cfg_sync: cover property ( f_cfg_sync );
   
   // ---------------------------------------------------------------------------      
   // f-playsync: f_playsync
   // ---------------------------------------------------------------------------
   
   property f_play_sync;
      logic txdata;      
      disable iff (rst_n == '0 || mrst_n == '0)       
	@(posedge clk) (1, txdata = play_in) |=> @(posedge mclk) 1 [* 0:CDC_BITSYNC_LATENCY] ##1 (txdata == play_out);
   endproperty

   af_play_sync: assert property ( f_play_sync )
     else $error("play_out sync failure.");
   cf_play_sync: cover property ( f_play_sync );
   

   // ---------------------------------------------------------------------------      
   // f-reqsync: f_reqsync
   // ---------------------------------------------------------------------------
   
   property f_req_sync;
      disable iff (rst_n == '0 || mrst_n == '0)       
	@(posedge mclk) $rose(req_in) |-> @(posedge clk) !req_out [* 1:CDC_PULSESYNC_LATENCY-1] ##1 req_out ##1 !req_out;
   endproperty

   af_req_sync: assert property ( f_req_sync )
     else $error("req_out sync failure.");
   cf_req_sync: cover property ( f_req_sync );
   
endmodule

`endif

