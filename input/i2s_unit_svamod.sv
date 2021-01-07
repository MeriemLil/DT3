`include "audioport.svh"

`ifndef SYNTHESIS

// If DUT is not a VHDL entity, comment this out
`define VHDL_DUT 1

import audioport_pkg::*;


package i2s_unit_pkg;
  typedef enum logic [2:0] { STOP, FILL, REQ, LOAD, PLAY} control_fsm_t;
endpackage
import i2s_unit_pkg::*;

   
module i2s_unit_svamod(
		       input logic 			   clk,
		       input logic 			   rst_n,
		       input logic 			   play_in,
		       input logic 			   tick_in, 
		       input logic [23:0] 		   audio_in_0,
		       input logic [23:0] 		   audio_in_1, 
		       input logic 			   cfg_in,
		       input logic [31:0] 		   cfg_reg_in,
		       
		       input logic 			   req_out,
		       input logic 			   ws_out,
		       input logic 			   sck_out,
		       input logic 			   sdo_out,

		       input logic [2:0] 		   sck_ctr_r,
		       input logic [3:0] 		   sck_mod_r, 
		       input logic [5:0] 		   ws_ctr_r,
		       input logic [47:0] 		   fifo_r [FIFO_SIZE-1:0],
`ifdef RTL_SIM
// The following works in simulation but fails in formal verification as Questa PropertyCheck
// uses a synthesized netlist of the design where extra bits of head_r and tail_r have been
// optimized away
		       input logic [31:0] 		   head_r,
		       input logic [31:0] 		   tail_r,
`else
// The following two lines generate a connection size mismatch warning in Questa Sim
// but they work both in simulation and formal verification
		       input logic [$clog2(FIFO_SIZE)-1:0] head_r,
		       input logic [$clog2(FIFO_SIZE)-1:0] tail_r, 
`endif
		       input logic [47:0]                  fifo_val,		   
		       input logic 			   looped_r,
		       input logic 			   empty,
		       input logic 			   full,
		       input logic [47:0] 		   out_srg_r,
		       input logic 			   sck_r,
		       input logic 			   ws_r,
		       input logic [2:0] 		   state_r_port,
		       input logic 			   out_srg_load,
		       input logic 			   out_srg_shift
		);

   // This trick is needed to bind a VHDL enum port to a SV port.
   control_fsm_t  state_r;
   assign state_r = control_fsm_t'(state_r_port);

   // ---------------------------------------------------------------------------      
   // Check for unknown 'x states (see xcheck macro definitions in audioport.svh)
   // ---------------------------------------------------------------------------      
     
   `xcheck(audio_in_0);
   `xcheck(audio_in_1);
   `xcheck(play_in);
   `xcheck(cfg_in);
   `xcheck(cfg_reg_in);
   `xcheck(req_out);
   `xcheck(ws_out);
   `xcheck(sck_out);
   `xcheck(sdo_out);   
   `xcheck(fifo_r);
   `xcheck(sck_ctr_r);
   `xcheck(sck_mod_r);
   `xcheck(ws_ctr_r);
   `xcheck(head_r);
   `xcheck(tail_r);
   `xcheck(looped_r);
   `xcheck(empty);
   `xcheck(full);
   `xcheck(out_srg_r);
   `xcheck(sck_r);
   `xcheck(ws_r);
   `xcheck(out_srg_load);
   `xcheck(out_srg_shift);

   //////////////////////////////////////////////////////////////////////////////
   //
   // Assumptions
   //
   //////////////////////////////////////////////////////////////////////////////   

`ifdef design_top_is_i2s_unit
   // ---------------------------------------------------------------------------   
   // f-tickin: tick_in_pulse
   // ---------------------------------------------------------------------------

   property f_tick_in_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(tick_in) |=> $fell(tick_in);
   endproperty

   mf_tick_in_pulse: assume property ( f_tick_in_pulse )
     else $error("Incorrect tick_in pulse.");

   // ---------------------------------------------------------------------------   
   // f-tickin: tick_in_play_only
   // ---------------------------------------------------------------------------

   property f_tick_in_play_only;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(tick_in) |-> play_in;
   endproperty

   mf_tick_in_play_only: assume property ( f_tick_in_play_only )
     else $error("tick_in pulse in non-play mode.");

   // ---------------------------------------------------------------------------   
   // f-tickin: tick_after_req
   // ---------------------------------------------------------------------------
   
   property f_tick_after_req;
      @(posedge clk) disable iff (rst_n == '0)
      play_in && req_out |=> (tick_in [-> 1:$]) or (!play_in [-> 1:$]);
   endproperty

   mf_tick_after_req: assume property (f_tick_after_req )
     else $error("No tick_in after req_out.");

   // ---------------------------------------------------------------------------   
   // f-tickin: req_before_tick
   // ---------------------------------------------------------------------------
   
   sequence s_req_before_tick;
      @(posedge clk)
	(play_in && req_out) ##1 play_in [*1:$];
   endsequence   

   property f_req_before_tick;
      @(posedge clk) disable iff (rst_n == '0)
	tick_in |-> !req_out && s_req_before_tick.triggered;
   endproperty

   mf_req_before_tick: assume property (f_req_before_tick )
     else $error("tick_in without req_out.");

   // ---------------------------------------------------------------------------   
   // f-start: play_1_length
   // ---------------------------------------------------------------------------

   localparam int MCLK_COMMAND_INTERVAL = int'((real'(CMD_WAIT_STATES)*CLK_PERIOD)/MCLK_PERIOD);
   
   property f_play_1_length;
      @(posedge clk) disable iff (rst_n == '0)
//	$rose(play_in) |=> play_in throughout ( $fell(ws_out) [-> 1] ##1 $fell(sck_out) [-> 1]);
	$rose(play_in) |-> play_in [* MCLK_COMMAND_INTERVAL];
   endproperty

   mf_play_1_length: assume property (f_play_1_length)
     else $error("play_in not kept high long enough.");

   // ---------------------------------------------------------------------------   
   // f-stop: play_0_length
   // ---------------------------------------------------------------------------
   
   property f_play_0_length;
      @(posedge clk) disable iff (rst_n == '0)
//	$fell(play_in) |-> (!play_in throughout ( !ws_out [-> 1])) ##1 !play_in [* 48*MCLK_DIV_48000 ];
	$fell(play_in) |-> !play_in [* MCLK_COMMAND_INTERVAL];
   endproperty

   mf_play_0_length: assume property (f_play_0_length)
    else $error("play_in not kept high long enough.");

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
   // f-cfgin: no_cfg_in_play
   // ---------------------------------------------------------------------------
   
   property f_no_cfg_in_play;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(tick_in) |-> play_in;
   endproperty

   mf_no_cfg_in_play: assume property ( f_no_cfg_in_play )
     else $error("cfg_in pulse in play mode.");

`endif
   
   //////////////////////////////////////////////////////////////////////////////
   //
   // Blackbox Assertions
   //
   //////////////////////////////////////////////////////////////////////////////   

   // ---------------------------------------------------------------------------   
   // f-waves: i2s_sck_wave
   // ---------------------------------------------------------------------------

   property sck_wave;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(sck_out) |=> (!sck_out) or
			   (sck_out ##1 !sck_out [* 2]) or
			   (sck_out [*3] ##1 !sck_out [* 4]);
   endproperty

   af_sck_wave: assert property ( sck_wave )
     else $error("Incorrect i2S SCK waveform.");
   cf_sck_wave: cover property ( sck_wave );
   
   // ---------------------------------------------------------------------------   
   // f-waves: first_cycle
   // ---------------------------------------------------------------------------
   
   property first_cycle;
      @(posedge clk) disable iff (rst_n == '0)
	(!sck_out [* MCLK_DIV_48000]) ##0 ($rose(play_in) ##1 (play_in throughout ( $rose(sck_out) [-> 1] ##1 $fell(sck_out) [-> 1]) )) |-> 
         (!ws_out         throughout ($rose(sck_out) [-> 23]))
     ##1 (!$rose(sck_out) throughout ($rose(ws_out) [-> 1]))
     ##1 (ws_out          throughout ($rose(sck_out) [-> 24]))
     ##1 (!$rose(sck_out) throughout ($fell(ws_out) [-> 1]));
   endproperty

   af_first_cycle: assert property ( first_cycle )
     else $error("Incorrect I2S WS waveform start.");
   cf_first_cycle: cover property ( first_cycle );
   

   // ---------------------------------------------------------------------------   
   // f-waves: middle_cycle
   // ---------------------------------------------------------------------------

   property middle_cycle;
      @(posedge clk) disable iff (rst_n == '0)
	(play_in && $fell(ws_out)) ##1 ((play_in && !ws_out) throughout ( $rose(sck_out)[-> 1] ##1 $fell(sck_out)[-> 1])) |=>
	     (!ws_out         throughout ($rose(sck_out) [-> 23]))
         ##1 (!$rose(sck_out) throughout ($rose(ws_out) [-> 1]))
         ##1 (ws_out          throughout ($rose(sck_out) [-> 24]))
         ##1 (!$rose(sck_out) throughout ($fell(ws_out) [-> 1]));					 
   endproperty

   af_middle_cycle: assert property ( middle_cycle )
     else $error("Incorrect full I2S WS waveform.");
   cf_middle_cycle: cover property ( middle_cycle );
   
   // ---------------------------------------------------------------------------   
   // f-waves, f-stop: last_cycle
   // ---------------------------------------------------------------------------
   
   property last_cycle;
      @(posedge clk) disable iff (rst_n == '0)
	$fell(ws_out) ##1 (!ws_out throughout ( $rose(sck_out)[-> 1] ##1 $fell(sck_out)[-> 1])) ##0 !$past(play_in) |->
					 (!ws_out && !sck_out) [* MCLK_DIV_48000];
   endproperty

   af_last_cycle: assert property ( last_cycle )
     else $error("Incorrect I2S WS waveform end.");
   cf_last_cycle: cover property ( last_cycle );
     
   // ---------------------------------------------------------------------------   
   // f-reqout: req_out_pulse
   // ---------------------------------------------------------------------------
   
   property req_out_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(req_out) |=> $fell(req_out);
   endproperty

   af_req_out_pulse: assert property ( req_out_pulse )
     else $error("Incorrect req_out pulse");
   cf_req_out_pulse: cover property ( req_out_pulse );
   
   // ---------------------------------------------------------------------------   
   // f-start: play_start
   // ---------------------------------------------------------------------------
   
   sequence s_sck_silent;
      @(posedge clk)
	(!sck_out [* MCLK_DIV_48000]);
   endsequence;

   sequence s_fifo_fill;
      @(posedge clk)
	play_in throughout ((($rose(req_out) [-> 1]) ##1 ($rose(tick_in) [-> 1])) [* FIFO_SIZE]) ##1 1 [* 0:3];
   endsequence;

   // Reasoning: If 'play_in' rose sck_out' has remained at '0 for some time; and then 'play_in' stays high untils
   // first edge of 'sck_out'; then a fifo fill sequence must have accured 0-3 cycles before.
   property play_start;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(play_in) ##0 s_sck_silent.triggered ##1 (play_in throughout $rose(sck_out) [-> 1]) 
	  |-> s_fifo_fill.triggered;
   endproperty

   af_play_start: assert property ( play_start )
     else $error("Incorrect playback start sequence.");
   cf_play_start: cover property ( play_start );
   
   // ---------------------------------------------------------------------------   
   // f-stop: play_stop
   // ---------------------------------------------------------------------------
   
   property play_stop;
      @(posedge clk) disable iff (rst_n == '0)
	($fell(ws_out) && $fell(sck_out)) ##1 !play_in throughout ( ($rose(sck_out) [-> 1]) ##1 ($fell(sck_out) [-> 1]) )
	   |=> (!ws_out && !sck_out && !sdo_out) throughout (play_in [-> 1]);
   endproperty

   af_play_stop: assert property ( play_stop )
     else $error("I2S waveforms did not stop after play_in = 0.");
   cf_play_stop: cover property ( play_stop );
   
   // ---------------------------------------------------------------------------   
   // f-wssync: sck_ws_sync
   // ---------------------------------------------------------------------------
   
   property sck_ws_sync;
      @(posedge clk) disable iff (rst_n == '0)
	!$stable(ws_out) |-> $fell(sck_out);
   endproperty

   af_sck_ws_sync: assert property ( sck_ws_sync )
     else $error("ws_out did not change on falling edge of sck_out.");
   cf_sck_ws_sync: cover property ( sck_ws_sync );
     
   // ---------------------------------------------------------------------------   
   // f-reqmore: req_out_seen
   // ---------------------------------------------------------------------------
   
   property req_out_seen;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(req_out) |=> not ((!req_out && play_in) throughout ($rose(sck_out) [-> 49]));
   endproperty
   
   af_req_out_seen: assert property ( req_out_seen )
     else $error("req_out pulse not generated during audio frame");
   cf_req_out_seen: cover property ( req_out_seen );
   

   //////////////////////////////////////////////////////////////////////////////
   //
   // Whitebox (RTL) Assertions
   //
   //////////////////////////////////////////////////////////////////////////////   
   
   // ---------------------------------------------------------------------------   
   // state_r transition checks
   // ---------------------------------------------------------------------------
   
   property r_STOP_STOP;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == STOP) && !play_in |=> state_r == STOP;
   endproperty

   ar_STOP_STOP: assert property ( r_STOP_STOP )
     else $error("state_r STOP => STOP failed.");
   cr_STOP_STOP: cover property ( r_STOP_STOP );

   property r_STOP_FILL;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == STOP) && play_in |=> state_r == FILL;
   endproperty

   ar_STOP_FILL: assert property ( r_STOP_FILL )
     else $error("state_r STOP => FILL failed.");
   cr_STOP_FILL: cover property ( r_STOP_FILL );
     
   property r_FILL_STOP;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == FILL) && !play_in |=> state_r == STOP;
   endproperty

   ar_FILL_STOP: assert property ( r_FILL_STOP )
     else $error("state_r FILL => STOP failed.");
   cr_FILL_STOP: cover property ( r_FILL_STOP );
     
   property r_FILL_REQ;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == FILL) && play_in && !full |=> state_r == REQ;
   endproperty

   ar_FILL_REQ: assert property ( r_FILL_REQ )
     else $error("state_r FILL => REQ failed.");
   cr_FILL_REQ: cover property ( r_FILL_REQ );
   
   property r_FILL_PLAY;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == FILL) && play_in && full |=> state_r == PLAY;
   endproperty

   ar_FILL_PLAY: assert property ( r_FILL_PLAY )
     else $error("state_r FILL => REQ failed.");
   cr_FILL_PLAY: cover property ( r_FILL_PLAY );
   
   property r_REQ_STOP;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == REQ) && !play_in |=> state_r == STOP;
   endproperty

   ar_REQ_STOP: assert property ( r_REQ_STOP )
     else $error("state_r REQ => STOP failed.");
   cr_REQ_STOP: cover property ( r_REQ_STOP );
     
   property r_REQ_LOAD;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == REQ) && play_in |=> state_r == LOAD;
   endproperty

   ar_REQ_LOAD: assert property ( r_REQ_LOAD )
     else $error("state_r REQ => LOAD failed.");
   cr_REQ_LOAD: cover property ( r_REQ_LOAD );
   
   property r_LOAD_STOP;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == LOAD) && !play_in |=> state_r == STOP;
   endproperty

   ar_LOAD_STOP: assert property ( r_LOAD_STOP )
     else $error("state_r LOAD => STOP failed.");
   cr_LOAD_STOP: cover property ( r_LOAD_STOP );
     
   property r_LOAD_LOAD;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == LOAD) && play_in && !tick_in |=> state_r == LOAD;
   endproperty

   ar_LOAD_LOAD: assert property ( r_LOAD_LOAD )
     else $error("state_r LOAD => LOAD failed.");
   cr_LOAD_LOAD: cover property ( r_LOAD_LOAD );
   
   property r_LOAD_FILL;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == LOAD) && play_in && tick_in |=> state_r == FILL;
   endproperty

   ar_LOAD_FILL: assert property ( r_LOAD_FILL )
     else $error("state_r LOAD => FILL failed.");
   cr_LOAD_FILL: cover property ( r_LOAD_FILL );
   
   property r_PLAY_STOP;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == PLAY) && !play_in && out_srg_load |=> state_r == STOP;
   endproperty

   ar_PLAY_STOP: assert property ( r_PLAY_STOP )
     else $error("state_r PLAY => STOP failed.");
   cr_PLAY_STOP: cover property ( r_PLAY_STOP );
   
   property r_PLAY_PLAY;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == PLAY) && ( (!play_in && !out_srg_load) || play_in) |=> state_r == PLAY;
   endproperty

   ar_PLAY_PLAY: assert property ( r_PLAY_PLAY )
     else $error("state_r PLAY => PLAY failed.");
   cr_PLAY_PLAY: cover property ( r_PLAY_PLAY );

   property r_load_sequence;
      @(posedge clk) disable iff (rst_n == '0)
	(play_in && (state_r == STOP)) |=>
	    ((state_r == FILL) ##1 (state_r == REQ) ##1 (state_r == LOAD) [* 1:48*(MCLK_DIV_48000)] ) [* FIFO_SIZE]
	     ##1 (state_r == FILL) ##1 (state_r == PLAY);
   endproperty

   cr_load_sequence: cover property ( r_load_sequence );
   
   // ---------------------------------------------------------------------------   
   // r_fifo_write
   // ---------------------------------------------------------------------------
     
   property r_fifo_write;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r != STOP) && tick_in && !full |=> fifo_r[$past(head_r)] == { $past(audio_in_0), $past(audio_in_1) };
   endproperty

   ar_fifo_write: assert property ( r_fifo_write )
     else $error("FIFO write failed.");
   cr_fifo_write: cover property ( r_fifo_write );

   // ---------------------------------------------------------------------------   
   // r_fifo_head_update
   // ---------------------------------------------------------------------------
     
   property r_fifo_head_update;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r != STOP) && tick_in && !full |=> head_r == ($past(head_r) + 1) % FIFO_SIZE;
   endproperty

   ar_fifo_head_update: assert property ( r_fifo_head_update )
     else $error("FIFO write failed.");

   // ---------------------------------------------------------------------------   
   // r_fifo_tail_update
   // ---------------------------------------------------------------------------
     
   property r_fifo_tail_update;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r != STOP) && out_srg_load && !empty |=> tail_r == ($past(tail_r) + 1) % FIFO_SIZE;
   endproperty

   ar_fifo_tail_update: assert property ( r_fifo_tail_update )
     else $error("FIFO write failed.");

   // ---------------------------------------------------------------------------   
   // r_fifo_looped_rise
   // ---------------------------------------------------------------------------
     
   property r_fifo_looped_rise;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r != STOP) && tick_in && !full && (head_r == FIFO_SIZE-1) |=> $rose(looped_r);
   endproperty

   ar_fifo_looped_rise: assert property ( r_fifo_looped_rise )
     else $error("FIFO looped_r did not rise.");

   // ---------------------------------------------------------------------------   
   // r_fifo_looped_fall
   // ---------------------------------------------------------------------------
     
   property r_fifo_looped_fall;
      @(posedge clk) disable iff (rst_n == '0)
	out_srg_load && !empty && (tail_r == FIFO_SIZE-1) |=> $fell(looped_r);
   endproperty

   ar_fifo_looped_fall: assert property ( r_fifo_looped_fall )
     else $error("FIFO looped_r did not fall.");
   
   // ---------------------------------------------------------------------------   
   // r_fifo_empty
   // ---------------------------------------------------------------------------
     
   property r_fifo_empty;
      @(posedge clk) disable iff (rst_n == '0)
	((head_r == tail_r) && !looped_r |-> empty)
	or
	(!((head_r == tail_r) && !looped_r) |-> !empty);
   endproperty

   ar_fifo_empty: assert property ( r_fifo_empty )
     else $error("FIFO empty in wrong state.");

   // ---------------------------------------------------------------------------   
   // r_fifo_full
   // ---------------------------------------------------------------------------
     
   property r_fifo_full;
      @(posedge clk) disable iff (rst_n == '0)
	((head_r == tail_r) && looped_r |-> full)
	or
	(!((head_r == tail_r) && looped_r) |-> !full);
   endproperty

   ar_fifo_full: assert property ( r_fifo_full )
     else $error("FIFO full in wring state..");
   
   // ---------------------------------------------------------------------------   
   // r_sck_mod_r_load
   // ---------------------------------------------------------------------------

    property r_sck_mod_r_load;
         @(posedge clk) disable iff (rst_n == '0)
	   (cfg_reg_in[1:0] == RATE_48000) && (state_r == STOP) && !play_in && cfg_in |=> (sck_mod_r == MCLK_DIV_48000)
	   or
	   (cfg_reg_in[1:0] == RATE_96000) && (state_r == STOP) && !play_in && cfg_in |=> (sck_mod_r == MCLK_DIV_96000)
	   or
	   (cfg_reg_in[1:0] == RATE_192000) && (state_r == STOP) && !play_in && cfg_in |=> (sck_mod_r == MCLK_DIV_192000);
    endproperty
      
   ar_sck_mod_r_load: assert property (r_sck_mod_r_load)
     else $error("sck_mod_r set to wrong value.");	
   cr_sck_mod_r_load: cover property (r_sck_mod_r_load);

   // ---------------------------------------------------------------------------   
   // r_sck_mod_r_stable
   // ---------------------------------------------------------------------------

    property r_sck_mod_r_stable;
         @(posedge clk) disable iff (rst_n == '0)
	   ((state_r != STOP) || !cfg_in)  |=> sck_mod_r == $past(sck_mod_r);
   endproperty
      
   ar_sck_mod_r_stable: assert property (r_sck_mod_r_stable)
     else $error("sck_mod_r did not remain stable.");	

   // ---------------------------------------------------------------------------   
   // r_sck_ctr_r_count
   // ---------------------------------------------------------------------------

    property r_sck_ctr_r_count;
         @(posedge clk) disable iff (rst_n == '0)
	   ((state_r == PLAY) && (sck_ctr_r != sck_mod_r-1) |=> sck_ctr_r == ($past(sck_ctr_r)  + 1))
	   or
	  ((state_r == PLAY) && (sck_ctr_r == sck_mod_r-1) |=> (sck_ctr_r == 0));
   endproperty
      
   ar_sck_ctr_r_count: assert property (r_sck_ctr_r_count)
     else $error("sck_ctr_r did no increment correctly.");	
	  
   // ---------------------------------------------------------------------------   
   // r_ws_ctr_r_count
   // ---------------------------------------------------------------------------
	 
   property r_ws_ctr_r_count;
     @(posedge clk) disable iff (rst_n == '0)
       ((state_r == PLAY) && (sck_ctr_r == sck_mod_r-1) && (ws_ctr_r < 47) |=> (ws_ctr_r == ($past(ws_ctr_r)  + 1)))
       or
       ((state_r == PLAY) && (sck_ctr_r == sck_mod_r-1) && (ws_ctr_r == 47) |=> (ws_ctr_r == 0));
   endproperty

   ar_ws_ctr_r_count: assert property (r_ws_ctr_r_count)
	else $error("ws_ctr_r did nor increment correctly.");	

   // ---------------------------------------------------------------------------   
   // r_ws_ctr_r_stable
   // ---------------------------------------------------------------------------

   property r_ws_ctr_r_stable;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == PLAY) && (sck_ctr_r != sck_mod_r-1) |=> (ws_ctr_r == $past(ws_ctr_r));
   endproperty

   ar_ws_ctr_r_stable: assert property (r_ws_ctr_r_stable)
      else $error("ws_ctr_r incremented at wrong time.");	

   // ---------------------------------------------------------------------------   
   // r_ws_ctr_r_clear
   // ---------------------------------------------------------------------------

   property r_ws_ctr_r_clear;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r != PLAY)  |=> (ws_ctr_r == 0);
   endproperty

   ar_ws_ctr_r_clear: assert property (r_ws_ctr_r_clear)
      else $error("ws_ctr_r did not reset when state_r != PLAY.");	

   // ---------------------------------------------------------------------------   
   // r_sck_r_load
   // ---------------------------------------------------------------------------

   property r_sck_r_load;
      @(posedge clk) disable iff (rst_n == '0)
       ((state_r == PLAY) && (sck_ctr_r < sck_mod_r/2)  |=> sck_r == '1)
       or
       (!((state_r == PLAY) && (sck_ctr_r < sck_mod_r/2))  |=> sck_r == '0);
   endproperty

   ar_sck_r_load: assert property (r_sck_r_load)
      else $error("sck_r nor correctly set.");	

   // ---------------------------------------------------------------------------   
   // r_sck_out_follow
   // ---------------------------------------------------------------------------

   property r_sck_out_follow;
      @(posedge clk) disable iff (rst_n == '0)
	sck_out == sck_r;
   endproperty

   ar_sck_out_follow: assert property (r_sck_out_follow)
      else $error("sck_out != sck_r.");	

   // ---------------------------------------------------------------------------   
   // r_sck_out_cycle
   // ---------------------------------------------------------------------------

   sequence s_sck_out_cycle (period);
      (sck_out [*period/2] ##1 !sck_out[*period/2]);
   endsequence   

   property r_sck_out_cycle(period);
      @(posedge clk) disable iff (rst_n == '0)
	$rose(sck_out) && (sck_mod_r == period) |-> s_sck_out_cycle(period);
   endproperty

   ar_sck_out_cycle_48kHz: assert property(r_sck_out_cycle(MCLK_DIV_48000))
     else $error("Malformed sck_out cycle in 48kHz mode.");
   ar_sck_out_cycle_96kHz: assert property(r_sck_out_cycle(MCLK_DIV_96000))
     else $error("Malformed sck_out cycle in 96kHz mode.");
   ar_sck_out_cycle_192kHz: assert property(r_sck_out_cycle(MCLK_DIV_192000))
     else $error("Malformed sck_out cycle in 192kHz mode.");

   cr_sck_out_cycle_48kHz: cover property(r_sck_out_cycle(MCLK_DIV_48000));
   cr_sck_out_cycle_96kHz: cover property(r_sck_out_cycle(MCLK_DIV_96000));
   cr_sck_out_cycle_192kHz: cover property(r_sck_out_cycle(MCLK_DIV_192000));
   
   // ---------------------------------------------------------------------------   
   // r_ws_r_load
   // ---------------------------------------------------------------------------

   property r_ws_r_load;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r == PLAY) && (sck_ctr_r == sck_mod_r/2) && (ws_ctr_r == 23 || ws_ctr_r == 47)  |=> ws_r == ~($past(ws_r));
   endproperty

   ar_ws_r_load: assert property (r_ws_r_load)
      else $error("ws_r nor correctly set.");	

   // ---------------------------------------------------------------------------   
   // r_ws_out_follow
   // ---------------------------------------------------------------------------

   property r_ws_out_follow;
      @(posedge clk) disable iff (rst_n == '0)
	ws_out == ws_r;
   endproperty

   ar_ws_out_follow: assert property (r_ws_out_follow)
      else $error("ws_out != ws_r.");	
 
   // ---------------------------------------------------------------------------   
   // r_ws_out_cycle
   // ---------------------------------------------------------------------------

   property r_ws_out_cycle(period);
      @(posedge clk) disable iff (rst_n == '0)
	$rose(ws_out) && (sck_mod_r == period)|-> ws_out [* 24*period] ##1 $fell(ws_out);
   endproperty      
      
   ar_ws_out_cycle_48kHz: assert property(r_ws_out_cycle(MCLK_DIV_48000))
     else $error("Short sck_out frame in 48kHz mode.");
   ar_ws_out_cycle_96kHz: assert property(r_ws_out_cycle(MCLK_DIV_96000))
     else $error("Short sck_out frame in 96kHz mode.");
   ar_ws_out_cycle_192kHz: assert property(r_ws_out_cycle(MCLK_DIV_192000))
     else $error("Short sck_out frame in 192kHz mode.");

   cr_ws_out_cycle_48kHz: cover property (r_ws_out_cycle(MCLK_DIV_48000));
   cr_ws_out_cycle_96kHz: cover property (r_ws_out_cycle(MCLK_DIV_96000));
   cr_ws_out_cycle_192kHz: cover property (r_ws_out_cycle(MCLK_DIV_192000));

   // ---------------------------------------------------------------------------   
   // r_out_srg_load_state
   // ---------------------------------------------------------------------------
     
   property r_out_srg_load_state;
      @(posedge clk) disable iff (rst_n == '0)
	((sck_ctr_r == sck_mod_r/2) && (ws_ctr_r == 0) |-> out_srg_load)
	or
	(!((sck_ctr_r == sck_mod_r/2) && (ws_ctr_r == 0)) |-> !out_srg_load);
   endproperty

   ar_out_srg_load_state: assert property ( r_out_srg_load_state )
     else $error("out_srg_load in wrong state.");

   // ---------------------------------------------------------------------------   
   // r_out_srg_shift_state
   // ---------------------------------------------------------------------------
     
   property r_out_srg_shift_state;
      @(posedge clk) disable iff (rst_n == '0)
	((sck_ctr_r == sck_mod_r/2) && !(ws_ctr_r == 0) |-> out_srg_shift)
	or
	(!((sck_ctr_r == sck_mod_r/2) && !(ws_ctr_r == 0)) |-> !out_srg_shift);
   endproperty

   ar_out_srg_shift_state: assert property ( r_out_srg_shift_state )
     else $error("out_srg_shift in wrong state.");

   // ---------------------------------------------------------------------------   
   // r_out_srg_r_load
   // ---------------------------------------------------------------------------
     
   property r_out_srg_r_load;
      @(posedge clk) disable iff (rst_n == '0)
	out_srg_load && !empty |=> out_srg_r == $past(fifo_r[$past(tail_r)]);
   endproperty

   ar_out_srg_r_load: assert property ( r_out_srg_r_load )
     else $error("out_srg_r not loaded correctly.");
   cr_out_srg_r_load: cover property ( r_out_srg_r_load );

   // ---------------------------------------------------------------------------   
   // r_out_srg_r_shift
   // ---------------------------------------------------------------------------
     
   property r_out_srg_r_shift;
      @(posedge clk) disable iff (rst_n == '0)
        !out_srg_load && out_srg_shift |=> out_srg_r == { $past(out_srg_r[46:0]), '0 };
   endproperty

   ar_out_srg_r_shift: assert property ( r_out_srg_r_shift )
     else $error("out_srg_r not shifted correctly.");
   cr_out_srg_r_shift: cover property ( r_out_srg_r_shift );

   // ---------------------------------------------------------------------------   
   // r_out_srg_r_stable
   // ---------------------------------------------------------------------------
     
   property r_out_srg_r_stable;
      @(posedge clk) disable iff (rst_n == '0)
	(state_r != PLAY && $stable(state_r)) && (!out_srg_load) && (!out_srg_shift) |=> out_srg_r == $past(out_srg_r); // no change

//	( !(!$stable(state_r) && state_r == STOP) && !(out_srg_load && !empty) && !out_srg_shift |=> out_srg_r == $past(out_srg_r)); // no change      
   endproperty

   ar_out_srg_r_stable: assert property ( r_out_srg_r_stable )
     else $error("out_srg_r state changed when it shouldn't.");

   // ---------------------------------------------------------------------------   
   // req_out_state
   // ---------------------------------------------------------------------------
     
   property r_req_out_state;
      @(posedge clk) disable iff (rst_n == '0)
	((state_r == REQ) || (state_r == PLAY && play_in && out_srg_load) |-> req_out)
	or
        (!((state_r == REQ) || (state_r == PLAY && play_in && out_srg_load)) |-> !req_out);
   endproperty

   ar_req_out_state: assert property ( r_req_out_state )
     else $error("req_out in wrong state.");

   // ---------------------------------------------------------------------------   
   // r_sdo_out follow
   // ---------------------------------------------------------------------------
   
   property r_sdo_out_follow;
      @(posedge clk) disable iff (rst_n == '0)
	sdo_out == out_srg_r[47];
   endproperty

   ar_sdo_out_follow: assert property (r_sdo_out_follow)
      else $error("sdo_out != out_srg_r[47].");	
        

   ////////////////////////////////////////////////////////////////////////////////////////////
   //
   // Covergroups
   //
   ///////////////////////////////////////////////////////////////////////////////////////////

   // ---------------------------------------------------------------------------   
   // Check that all sample rates are set
   // ---------------------------------------------------------------------------
      
   covergroup cg_cfg_reg_in @(posedge clk iff (!play_in && cfg_in));
      coverpoint cfg_reg_in[1:0]
	{
	 bins valid_rates[] =  { RATE_48000, RATE_96000, RATE_192000 };
	 bins others[] = default;
	 }
   endgroup

   cg_cfg_reg_in cg_cfg_reg_in_inst = new;   

   // ---------------------------------------------------------------------------   
   // Check that all sample rates are use
   // ---------------------------------------------------------------------------
   
   covergroup cg_sck_mod @(posedge clk iff (state_r == PLAY));
      coverpoint sck_mod_r
	{
	 bins rates[] =  { MCLK_DIV_48000, MCLK_DIV_96000, MCLK_DIV_192000 };
	 }
   endgroup
   
   cg_sck_mod cg_sck_mod_inst = new;   

   // ---------------------------------------------------------------------------   
   // Check that all input bits had both values
   // ---------------------------------------------------------------------------
   
   covergroup cg_input_bits (string name, input int index, ref logic [47:0] audiobits) with function sample();
      option.per_instance = 1;
      option.name = name;
      bitpos: coverpoint audiobits[index];
   endgroup

   // Process for creating instances and sampling
   initial
     begin
	cg_input_bits inst[48];

	// Create covergroup instances, one per bit
	for(int i = 0; i < 48; ++i)
	   inst[i] = new($sformatf("bit%0d", i), i, {audio_in_1, audio_in_0});

	// Sample covergroups when tick_in == '1
	forever @(posedge clk)
	  for(int i = 0; i < 48; ++i) 
	    if (tick_in) inst[i].sample();
     end   

   // ---------------------------------------------------------------------------   
   // Check that all srg bits had both values in in all sample rate modes
   // ---------------------------------------------------------------------------
   
   covergroup cg_srg_bits_rates (string name, input int index, ref logic [47:0] audiobits, ref logic [3:0] sck_mod) 
     with function sample(logic [47:0] x, logic [3:0] y);
      option.per_instance = 1;
      option.name = name;
      bit_toggles: coverpoint audiobits[index]
	{
	 bins toggles[] = ( '0 => '1 ), ( '1 => '0 );
	 }
      rates: coverpoint sck_mod
	{
	 bins rates[] =  { MCLK_DIV_48000, MCLK_DIV_96000, MCLK_DIV_192000 };
        }
      toggles_per_rate: cross bit_toggles, rates;
   endgroup

   // Process for creating instances and sampling   
   initial
     begin
	cg_srg_bits_rates inst[48];

	// Create covergroup instances, one per bit
	for(int i = 0; i < 48; ++i)
	   inst[i] = new($sformatf("bit%0d", i), i, fifo_val, sck_mod_r);

	// Sample covergroups when shift register is loaded
	forever @(posedge clk)
	  for(int i = 0; i < 48; ++i) 
	    if (out_srg_load) inst[i].sample(fifo_val, sck_mod_r);
     end   

endmodule

`endif
