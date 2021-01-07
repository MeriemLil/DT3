`include "audioport.svh"

`ifndef SYNTHESIS

import audioport_pkg::*;

module control_unit_svamod
  
  (input logic clk,
   input logic 				       rst_n,

   /////////////////////////////////////////////
   // Module ports
   /////////////////////////////////////////////

   // APB and irq_out
   input logic 				       psel_in,
   input logic 				       penable_in,
   input logic 				       pwrite_in,
   input logic [31:0] 			       paddr_in,
   input logic [31:0] 			       pwdata_in,
   input logic [31:0] 			       prdata_out,
   input logic 				       pready_out,
   input logic 				       pslverr_out,
   input logic 				       irq_out,
   input logic [1:0][23:0] 		       abuf_out,
   input logic 				       cfg_out,
   input logic [31:0] 			       cfg_reg_out,
   input logic 				       level_out,
   input logic [31:0] 			       level_reg_out,
   input logic [DSP_REGISTERS-1:0][31:0]       dsp_regs_out,
   input logic 				       clr_out,
   input logic 				       tick_out,
   input logic 				       play_out,
   input logic 				       req_in,

   /////////////////////////////////////////////
   // Module variables
   /////////////////////////////////////////////

   input logic [INT_ADDR_BITS-1:0] 	       int_addr, 
   input logic 				       write,
   input logic 				       ready,
   input logic [$clog2(CMD_WAIT_STATES):0]     wait_counter_r,
   input logic [AUDIOPORT_REGISTERS-1:0][31:0] rbank_r,
   input logic 				       start,
   input logic 				       stop,
   input logic 				       clr

   // To do: Add inputs for ABUF LOGIC variables
   );

   // ---------------------------------------------------------------------------      
   // Check for unknown 'x states (see xcheck macro definitions in audioport.svh)
   // ---------------------------------------------------------------------------      
   
   `xcheck(psel_in);
   `xcheck(penable_in);
   `xcheck(pwrite_in);
   `xcheck(paddr_in);
   `xcheck(pwdata_in);
   `xcheck(prdata_out);
   `xcheck(pready_out);
   `xcheck(pslverr_out);
   `xcheck(irq_out);
   `xcheck(abuf_out);
   `xcheck(cfg_reg_out);
   `xcheck(level_reg_out);
   `xcheck(dsp_regs_out);
   `xcheck(clr_out);
   `xcheck(tick_out);
   `xcheck(play_out);
   `xcheck(req_in);
   `xcheck(int_addr);
   `xcheck(write);
   `xcheck(wait_counter_r);
   `xcheck(ready);
   `xcheck(start);
   `xcheck(stop);
   `xcheck(clr);   
   `xcheck(rbank_r);   

   
   //////////////////////////////////////////////////////////////////////////////
   //
   // 1. Assumptions for formal verification
   //
   //////////////////////////////////////////////////////////////////////////////

 `ifdef design_top_is_control_unit
   
 `include "apb_assumes.svh"
   
   // ---------------------------------------------------------------------------      
   // f_req_pulse
   // ---------------------------------------------------------------------------      

   property f_req_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(req_in) |=> !req_in;
   endproperty
   
   mf_req_pulse: assume property(f_req_pulse)
     else $error("req_in pulse width was not one clock cycle");

   // ---------------------------------------------------------------------------      
   // f_first_req_in
   // ---------------------------------------------------------------------------      

   property f_first_req_in;
      @(posedge clk) disable iff (rst_n == '0)
	;
   endproperty
   
   mf_first_req_in: assume property(f_first_req_in)
     else $error("req_in too soon after CMD_START");

`endif
   
   //////////////////////////////////////////////////////////////////////////////
   //
   // 2. Blackbox Assertions
   //
   //////////////////////////////////////////////////////////////////////////////

   // ---------------------------------------------------------------------------      
   // f-bus-unselect: f_prdata_unselected
   // ---------------------------------------------------------------------------

   property f_prdata_unselect;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty
      
   af_prdata_unselect: assert property(f_prdata_unselect)
     else $error("prdata_out not zero when psel_in == '0");
   cf_prdata_unselect: cover property(f_prdata_unselect);
   
   // ---------------------------------------------------------------------------      
   // f-bus-waitstates: f_cmd_reg_write
   // ---------------------------------------------------------------------------

   property f_cmd_reg_write;
      @(posedge clk) disable iff (rst_n == '0)
	(psel_in && pwrite_in && !penable_in && (paddr_in == CMD_REG_APB_ADDRESS)) |=>
					 ( !pready_out [* CMD_WAIT_STATES] ##1 pready_out);
   endproperty
      
   af_cmd_reg_write: assert property(f_cmd_reg_write)
     else $error("Wait states not correctly generated when CMD_REG was written to.");
   cf_cmd_reg_write: cover property(f_cmd_reg_write);

   // ---------------------------------------------------------------------------      
   // f-cfgreg: f_cfg_reg_write
   // ---------------------------------------------------------------------------

   property f_cfg_reg_write;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty
      
   af_cfg_reg_write: assert property(f_cfg_reg_write)
     else $error("cfg_reg_out value differs from value written to CFG_REG");
   cf_cfg_reg_write: cover property(f_cfg_reg_write);
   
   // ---------------------------------------------------------------------------            
   // f-levelreg: level_reg_write
   // ---------------------------------------------------------------------------      
      
   property f_level_reg_write;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty
      
   af_level_reg_write: assert property(f_level_reg_write)
     else $error("level_reg_reg_out value differs from value written to LEVEL_REG");
   cf_level_reg_write: cover property(f_level_reg_write);

   // ---------------------------------------------------------------------------            
   // f-dspregs: f_dsp_regs_write
   // ---------------------------------------------------------------------------      
      
   property f_dsp_regs_write;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty
      
   af_dsp_regs_write: assert property(f_dsp_regs_write)
     else $error("dsp_regs_reg_out value differs from value written to DSP_REGS");
   cf_dsp_regs_write: cover property(f_dsp_regs_write);

   // ---------------------------------------------------------------------------            
   // f-command: f_cfg_pulse
   // ---------------------------------------------------------------------------            

   property f_cfg_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty
   
   af_cfg_pulse: assert property(f_cfg_pulse)
     else $error("cfg_out pulse not correctly generated after CMD_CFG");
   cf_cfg_pulse: cover property(f_cfg_pulse);

   // ---------------------------------------------------------------------------            
   // f-command: f_cfg_no_pulse
   // ---------------------------------------------------------------------------            

   property f_cfg_no_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty
   
   af_cfg_no_pulse: assert property(f_cfg_no_pulse)
     else $error("cfg_out was high while play_oue == '1 or no CMD_CFG");
   cf_cfg_no_pulse: cover property(f_cfg_no_pulse);
				 
   // ---------------------------------------------------------------------------      	 
   // f-command: f_level_pulse
   // ---------------------------------------------------------------------------      

   property f_level_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty

   af_level_pulse: assert property(f_level_pulse)
     else $error("level_out pulse not correctly generated after CMD_LEVEL");
   cf_level_pulse: cover property(f_level_pulse);

   // ---------------------------------------------------------------------------      	 
   // f-command: f_level_no_pulse
   // ---------------------------------------------------------------------------      

   property f_level_no_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty

   af_level_no_pulse: assert property(f_level_no_pulse)
     else $error("level_out high while no CMD_LEVEL");
   cf_level_no_pulse: cover property(f_level_no_pulse);
   
   // ---------------------------------------------------------------------------      	 
   // f-command: f_clr_pulse
   // ---------------------------------------------------------------------------      

   property f_clr_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty

   af_clr_pulse: assert property(f_clr_pulse)
     else $error("clr_out pulse not correctly generated after CMD_CLR");
   cf_clr_pulse: cover property(f_clr_pulse);

   // ---------------------------------------------------------------------------      	 
   // f-command: f_clr_no_pulse
   // ---------------------------------------------------------------------------      

   property f_clr_no_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty

   af_clr_no_pulse: assert property(f_clr_no_pulse)
     else $error("clr_out was while play_out == '1 or no CMD_CLR");
   cf_clr_no_pulse: cover property(f_clr_no_pulse);

   // ---------------------------------------------------------------------------      	 
   // f-command: f_illegal_command
   // ---------------------------------------------------------------------------      

   property f_illegal_command;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty

   af_illegal_command: assert property(f_illegal_command)
     else $error("Illegal command cause one command signalto rise");
   cf_illegal_command: cover property(f_illegal_command);
   
   // ---------------------------------------------------------------------------      
   // f-tick: f_tick_pulse
   // ---------------------------------------------------------------------------      

   property f_tick_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	1;
   endproperty
   
   af_tick_pulse: assert property(f_tick_pulse)
     else $error("tick_out pulse width was not one clock cycle");
   cf_tick_pulse: cover property(f_tick_pulse);

   // ---------------------------------------------------------------------------      
   // f-intr: f_irq_out_rise_first
   // ---------------------------------------------------------------------------      

   property f_irq_out_rise_first;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_irq_out_rise_first: assert property(f_irq_out_rise_first)
     else $error("irq_out did not rise after %d tick_out pulses", AUDIO_BUFFER_SIZE);
   cf_irq_out_rise_first: cover property(f_irq_out_rise_first);

   // ---------------------------------------------------------------------------      
   // f-intr: f_irq_out_rise_other
   // ---------------------------------------------------------------------------      

   property f_irq_out_rise_other;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_irq_out_rise_other: assert property(f_irq_out_rise_other)
     else $error("irq_out did not rise_other after %d tick_out pulses", AUDIO_BUFFER_SIZE);
   cf_irq_out_rise_other: cover property(f_irq_out_rise_other);
   
   // ---------------------------------------------------------------------------      
   // f-intr: f_irq_out_length
   // ---------------------------------------------------------------------------      

   property f_irq_out_length;
      @(posedge clk ) disable iff (rst_n == '0)
	  1;
   endproperty

   af_irq_out_length: assert property(f_irq_out_length)
     else $error("irq_out length did not stay '1 long enough");
   cf_irq_out_length: cover property(f_irq_out_length);

   // ---------------------------------------------------------------------------      
   // f-intr: irq_out_clear
   // ---------------------------------------------------------------------------      

   property f_irq_out_clear;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty
      
   af_irq_out_clear: assert property(f_irq_out_clear)
     else $error("irq_out not cleared after write to abif or CMD_CLR command");
   cf_irq_out_clear: cover property(f_irq_out_clear);

   //////////////////////////////////////////////////////////////////////////////
   //
   // 3. White-Box Assertions
   //
   //////////////////////////////////////////////////////////////////////////////

   // ---------------------------------------------------------------------------      
   // r-int_addr: r_int_addr_set
   // ---------------------------------------------------------------------------      

   property r_int_addr_set;
      @(posedge clk) disable iff (rst_n == '0)
	psel_in |-> (int_addr == (paddr_in - AUDIOPORT_START_APB_ADDRESS)/4);
   endproperty

   ar_int_addr_set: assert property(r_int_addr_set)
     else $error("int_addr incorrect during rbank access.");
   cr_int_addr_set: cover property(r_int_addr_set);
   
   // ---------------------------------------------------------------------------      
   // r-int_addr: r_int_addr_notset
   // ---------------------------------------------------------------------------      

   property r_int_addr_not_set;
      @(posedge clk) disable iff (rst_n == '0)
	!psel_in |-> (int_addr == 0);
   endproperty

   ar_int_addr_not_set: assert property(r_int_addr_not_set)
     else $error("int_addr not zero when psel_in == '0.");
   cr_int_addr_not_set: cover property(r_int_addr_not_set);
   
   // ---------------------------------------------------------------------------      
   // r-write: r_write_pulse
   // ---------------------------------------------------------------------------      
   
   property r_write_pulse;
      @(posedge clk) disable iff (rst_n == '0)
	(psel_in && penable_in && pwrite_in && pready_out |-> write ##1 !write)
	or
	(!(psel_in && penable_in && pwrite_in && pready_out) |-> !write);
   endproperty

   ar_write_pulse: assert property(r_write_pulse)
     else $error("'write' value is incorrect.");
   cr_write_pulse: cover property(r_write_pulse);

   // ---------------------------------------------------------------------------      
   // r-wait_counter (a): r_wait_counter_off
   // ---------------------------------------------------------------------------      
   
   property r_wait_counter_off;
      @(posedge clk) disable iff (rst_n == '0)
	!psel_in || !(pwrite_in && (int_addr == CMD_REG_INT_ADDRESS)) |=> (wait_counter_r == 0);
   endproperty

   ar_wait_counter_off: assert property(r_wait_counter_off)
     else $error("wait_counter_r not zero when no CMD_REG write is active.");
   cr_wait_counter_off: cover property(r_wait_counter_off);
   
   // ---------------------------------------------------------------------------      
   // r-wait_counter (b): r_wait_counter_start
   // ---------------------------------------------------------------------------      
   
   property r_wait_counter_start;
      @(posedge clk) disable iff (rst_n == '0)
	(wait_counter_r == 0) && psel_in && !penable_in && pwrite_in && (int_addr == CMD_REG_INT_ADDRESS) |=> (wait_counter_r == 1);
   endproperty

   ar_wait_counter_start: assert property(r_wait_counter_start)
     else $error("wait_counter_r not set to 1 on CMD_REG write access.");
   cr_wait_counter_start: cover property(r_wait_counter_start);
   
   // ---------------------------------------------------------------------------      
   // r-wait_counter (c): r_wait_counter_inc
   // ---------------------------------------------------------------------------      
   
   property r_wait_counter_inc;
      @(posedge clk) disable iff (rst_n == '0)
	((wait_counter_r > 0) && (wait_counter_r < CMD_WAIT_STATES)) |=> (wait_counter_r == $past(wait_counter_r)+1);
   endproperty

   ar_wait_counter_inc: assert property(r_wait_counter_inc)
     else $error("wait_counter_r not incremented.");
   cr_wait_counter_inc: cover property(r_wait_counter_inc);
   
   // ---------------------------------------------------------------------------      
   // r-wait_counter (d): r_wait_counter_stop
   // ---------------------------------------------------------------------------      
   
   property r_wait_counter_stop;
      @(posedge clk) disable iff (rst_n == '0)
	(wait_counter_r >= CMD_WAIT_STATES) |=> (wait_counter_r == 0);
   endproperty

   ar_wait_counter_stop: assert property(r_wait_counter_stop)
     else $error("wait_counter_r did not roll banck to 0.");
   cr_wait_counter_stop: cover property(r_wait_counter_stop);
   
   // ---------------------------------------------------------------------------      
   // r-ready: r_ready_value_0
   // ---------------------------------------------------------------------------      
   
   property r_ready_value_0;
      @(posedge clk) disable iff (rst_n == '0)
        ((wait_counter_r != 0) |-> !ready);
   endproperty

   ar_ready_value_0: assert property(r_ready_value_0)
     else $error("'ready' value is incorrect.");
   cr_ready_value_0: cover property(r_ready_value_0);
     
   // ---------------------------------------------------------------------------      
   // r-ready: r_ready_value_1
   // ---------------------------------------------------------------------------      
   
   property r_ready_value_1;
      @(posedge clk) disable iff (rst_n == '0)
	((wait_counter_r == 0) |-> ready);
   endproperty

   ar_ready_value_1: assert property(r_ready_value_1)
     else $error("'ready' value is incorrect.");
   cr_ready_value_1: cover property(r_ready_value_1);
   
   // ---------------------------------------------------------------------------      
   // r-pready: r_pready_follow
   // ---------------------------------------------------------------------------      
   
   property r_pready_follow;
      @(posedge clk) disable iff (rst_n == '0)
	pready_out == ready;
   endproperty

   ar_pready_follow: assert property(r_pready_follow)
     else $error("pready_out != ready.");
   cr_pready_follow: cover property(r_pready_follow);
   
   // ---------------------------------------------------------------------------      
   // r-pslverr: r_pslverr_0
   // ---------------------------------------------------------------------------      
   
   property r_pslverr_is_0;
      @(posedge clk) disable iff (rst_n == '0)
	pslverr_out == '0;
   endproperty

   ar_pslverr_is_0: assert property(r_pslverr_is_0)
     else $error("pslverr_out != '0.");
   cr_pslverr_is_0: cover property(r_pslverr_is_0);
   
   // ---------------------------------------------------------------------------      
   // r-bank (a): r_rbank_write
   // ---------------------------------------------------------------------------      
   
   property r_rbank_write;
      @(posedge clk) disable iff (rst_n == '0)
	write |=> rbank_r[$past(int_addr)] == $past(pwdata_in);
   endproperty

   ar_rbank_write: assert property(r_rbank_write)
     else $error("Write to rbank failed.");
   cr_rbank_write: cover property(r_rbank_write);

   // ---------------------------------------------------------------------------      
   // r-bank (b): r_rbank_clear
   // ---------------------------------------------------------------------------      
   
   property r_rbank_clear;
      @(posedge clk) disable iff (rst_n == '0)
	clr |=> {rbank_r}[(ABUF1_END_INT_ADDRESS)*32+31 : (ABUF0_START_INT_ADDRESS)*32] == 0;
   endproperty

   ar_rbank_clear: assert property(r_rbank_clear)
     else $error("CMD_CLR dis not set ABUF registers to 0.");
   cr_rbank_clear: cover property(r_rbank_clear);
   
   // ---------------------------------------------------------------------------      
   // r-bank (c): r_rbank_stable
   // ---------------------------------------------------------------------------      
   
   property r_rbank_stable;
      @(posedge clk) disable iff (rst_n == '0)
	!write && !clr |=> rbank_r == $past(rbank_r);
   endproperty

   ar_rbank_stable: assert property(r_rbank_stable)
     else $error("rbank_r state changed while !write && !clr");
   cr_rbank_stable: cover property(r_rbank_stable);
   
   // ---------------------------------------------------------------------------      
   // r-prdata_mux: r_prdata_value_set
   // ---------------------------------------------------------------------------      
      
   property r_prdata_value_set;
      @(posedge clk) disable iff (rst_n == '0)
	(psel_in	|-> prdata_out == rbank_r[int_addr]);
   endproperty

   ar_prdata_value_set: assert property(r_prdata_value_set)
     else $error("prdata_out valu is incorrect.");
   cr_prdata_value_set: cover property(r_prdata_value_set);
   
   // ---------------------------------------------------------------------------      
   // r-prdata_mux: r_prdata_value_0
   // ---------------------------------------------------------------------------      
      
   property r_prdata_value_0;
      @(posedge clk) disable iff (rst_n == '0)
	!psel_in |-> prdata_out == 0;
   endproperty

   ar_prdata_value_0: assert property(r_prdata_value_0)
     else $error("prdata_out valu is incorrect.");
   cr_prdata_value_0: cover property(r_prdata_value_0);
   
   // ---------------------------------------------------------------------------      
   // r-level_reg_out: r_level_reg_out_follow
   // ---------------------------------------------------------------------------      

   property r_level_reg_out_follow;
      @(posedge clk ) disable iff (rst_n == '0)
	level_reg_out == rbank_r[LEVEL_REG_INT_ADDRESS];
   endproperty
   
   ar_level_reg_out_follow: assert property(r_level_reg_out_follow)
     else $error("level_reg_out does not show LEVEL_REG contents");
   cr_level_reg_out_follow: cover property(r_level_reg_out_follow);
     
   // ---------------------------------------------------------------------------      
   // r-cfg_reg_out: r_cfg_reg_out_follow
   // ---------------------------------------------------------------------------      
 
    property r_cfg_reg_out_follow;
      @(posedge clk ) disable iff (rst_n == '0)
        cfg_reg_out == rbank_r[CFG_REG_INT_ADDRESS];
    endproperty

    ar_cfg_reg_out_follow: assert property(r_cfg_reg_out_follow)
      else $error("cfg_reg_out does not show CFG_REG contents");
   cr_cfg_reg_out_follow: cover property(r_cfg_reg_out_follow);
   
   // ---------------------------------------------------------------------------      
   // 7. r-dsp_regs_out: r_dsp_regs_out_follow
   // ---------------------------------------------------------------------------      

   property r_dsp_regs_out_follow;
      @(posedge clk ) disable iff (rst_n == '0)
	dsp_regs_out == rbank_r[DSP_REGS_END_INT_ADDRESS:DSP_REGS_START_INT_ADDRESS];
   endproperty
   
   ar_dsp_regs_out_follow: assert property(r_dsp_regs_out_follow)
     else $error("dsp_regs_out does not show DSP_REGS contents");
   cr_dsp_regs_out_follow: cover property(r_dsp_regs_out_follow);
   
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (a) r_cmd_onehot0
   // ---------------------------------------------------------------------------      
      
   property r_cmd_onehot0;
      @(posedge clk ) disable iff (rst_n == '0)
	(write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] inside { CMD_CLR, CMD_CFG, CMD_START, CMD_STOP, CMD_LEVEL }))
	 |-> $onehot0( { start, stop, cfg_out, level_out, clr_out } );
   endproperty
   
   ar_cmd_onehot0: assert property(r_cmd_onehot0)
     else $error("More than one command signals have value '1");
   cr_cmd_onehot0: cover property(r_cmd_onehot0);
   
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_clr_pulse
   // ---------------------------------------------------------------------------      
      
   property r_clr_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	((write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_CLR) && !play_out)
	 |-> clr ##1 !clr);
   endproperty
   
   ar_clr_pulse: assert property(r_clr_pulse)
     else $error("clr pulse not correctly generated.");
   cr_clr_pulse: cover property(r_clr_pulse);
   
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_no_clr
   // ---------------------------------------------------------------------------      
      
   property r_no_clr;
      @(posedge clk ) disable iff (rst_n == '0)
	(!(write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_CLR) && !play_out)
	 |-> !clr);
   endproperty
   
   ar_no_clr: assert property(r_no_clr)
     else $error("clr value incorrect.");
   cr_no_clr: cover property(r_no_clr);
   
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_cfg_pulse
   // ---------------------------------------------------------------------------      
      
   property r_cfg_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	((write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_CFG) && !play_out)
	 |-> cfg_out ##1 !cfg_out);
   endproperty
   
   ar_cfg_pulse: assert property(r_cfg_pulse)
     else $error("cfg_out pulse not correctly generated.");
   cr_cfg_pulse: cover property(r_cfg_pulse);
     
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_no_cfg
   // ---------------------------------------------------------------------------      
      
   property r_no_cfg;
      @(posedge clk ) disable iff (rst_n == '0)
	(!(write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_CFG) && !play_out)
	 |-> !cfg_out);
   endproperty
   
   ar_no_cfg: assert property(r_no_cfg)
     else $error("cfg_out valu incorrect.");
   cr_no_cfg: cover property(r_no_cfg);
   
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_start_pulse
   // ---------------------------------------------------------------------------      
      
   property r_start_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	((write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_START))
	 |-> start ##1 !start);
   endproperty
   
   ar_start_pulse:  assert property(r_start_pulse)
     else $error("start pulse not correctly generated.");
   cr_start_pulse:  cover property(r_start_pulse);
    
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_no_start
   // ---------------------------------------------------------------------------      
      
   property r_no_start;
      @(posedge clk ) disable iff (rst_n == '0)
	(!(write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_START))
	 |-> !start);
   endproperty
   
   ar_no_start: assert property(r_no_start)
     else $error("start value incorrect.");
   cr_no_start: cover property(r_no_start);
    
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_stop_pulse
   // ---------------------------------------------------------------------------      
      
   property r_stop_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	((write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_STOP))
	 |-> stop ##1 !stop);
   endproperty
   
   ar_stop_pulse:  assert property(r_stop_pulse)
     else $error("stop pulse not correctly generated.");
   cr_stop_pulse:  cover property(r_stop_pulse);
   
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_no_stop
   // ---------------------------------------------------------------------------      
      
   property r_no_stop;
      @(posedge clk ) disable iff (rst_n == '0)
	(!(write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_STOP))
	 |-> !stop);
   endproperty
   
   ar_no_stop: assert property(r_no_stop)
     else $error("stop value incorrect.");
   cr_no_stop: cover property(r_no_stop);
   
   
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_level_pulse
   // ---------------------------------------------------------------------------      
      
   property r_level_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	((write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_LEVEL))
	 |-> level_out ##1 !level_out);
   endproperty
   
   ar_level_pulse: assert property(r_level_pulse)
     else $error("level_out pulse not correctly generated.");
   cr_level_pulse: cover property(r_level_pulse);
   
   // ---------------------------------------------------------------------------      	 
   // r-command_decode (b) r_no_level
   // ---------------------------------------------------------------------------      
      
   property r_no_level;
      @(posedge clk ) disable iff (rst_n == '0)
	(!(write && (int_addr == CMD_REG_INT_ADDRESS) && (pwdata_in[31:24] == CMD_LEVEL))
	 |-> !level_out);
   endproperty
   
   ar_no_level: assert property(r_no_level)
     else $error("level_out value incorrect.");
   cr_no_level: cover property(r_no_level);
   
   // ---------------------------------------------------------------------------      
   // r-clr_out: r_clr_follow
   // ---------------------------------------------------------------------------      
   
   property r_clr_follow;
      @(posedge clk) disable iff (rst_n == '0)
	clr_out == clr;
   endproperty

   ar_clr_follow: assert property(r_clr_follow)
     else $error("clr_out != clr.");
   cr_clr_follow: cover property(r_clr_follow);
   
   
   //////////////////////////////////////////////////////////////////////////////
   //
   // Covergroups
   //
   //////////////////////////////////////////////////////////////////////////////

 `ifdef RTL_SIM

   // ---------------------------------------------------------------------------      
   // cg_apb_write
   // ---------------------------------------------------------------------------      
      

   // ---------------------------------------------------------------------------      
   // cg_apb_read
   // ---------------------------------------------------------------------------      
      

   // ---------------------------------------------------------------------------      
   // cg_commands
   // ---------------------------------------------------------------------------      
      

 `endif //  `ifdef RTL_SIM
   
endmodule
  
`endif //  `ifndef SYNTHESIS
   
