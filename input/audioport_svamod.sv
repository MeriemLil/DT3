
`include "audioport.svh"

`ifndef SYNTHESIS

import audioport_pkg::*;

module audioport_svamod
  
  (input logic clk,
   input logic 				  rst_n,
   input logic 				  mclk,
   input logic 				  mrst_n,
   input logic 				  psel_in,
   input logic 				  penable_in,
   input logic 				  pwrite_in,
   input logic [31:0] 			  paddr_in,
   input logic [31:0] 			  pwdata_in,
   input logic [31:0] 			  prdata_out,
   input logic 				  pready_out,
   input logic 				  pslverr_out,
   input logic 				  irq_out,
   input logic 				  ws_out,
   input logic 				  sck_out, 
   input logic 				  sdo_out,
   input logic 				  test_mode_sel,
   input logic 				  tick,
   input logic 				  play,
   input logic 				  req,
   input logic 				  cfg,
   input logic 				  level,
   input logic 				  clr,
   input logic [1:0][23:0] 		  abuf,
   input logic [1:0][23:0] 		  dsp,
   input logic 				  dsp_tick,
   input logic [31:0] 			  cfg_reg,
   input logic [31:0] 			  level_reg,
   input logic [DSP_REGISTERS-1:0][31:0] dsp_regs,
   input logic 				  mtick,
   input logic 				  mplay,
   input logic 				  mreq,
   input logic 				  mcfg, 
   input logic [31:0] 			  mcfg_reg,
   input logic [1:0][23:0] 		  mdsp
   );

   // ---------------------------------------------------------------------------      
   // Check for unknown 'x states (see xcheck macro definitions in audioport.svh)
   // Notice mclk domain signals are checked using xcheckm
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
   `xcheckm(sck_out);
   `xcheckm(ws_out);
   `xcheckm(sdo_out);
   `xcheckm(test_mode_sel);   
   `xcheck(tick);
   `xcheck(play);
   `xcheck(req);
   `xcheck(cfg);
   `xcheck(level);
   `xcheck(clr);
   `xcheck(abuf);
   `xcheck(dsp);
   `xcheck(dsp_tick);
   `xcheck(cfg_reg);
   `xcheck(level_reg);
   `xcheck(dsp_regs);
   `xcheckm(mtick);
   `xcheckm(mplay);
   `xcheckm(mreq);
   `xcheckm(mcfg);   
   `xcheckm(mcfg_reg);
   `xcheckm(mdsp);

   //////////////////////////////////////////////////////////////////////////////
   //
   // 1. Assumptions for formal verification
   //
   //////////////////////////////////////////////////////////////////////////////

 `include "apb_assumes.svh"
   
   //////////////////////////////////////////////////////////////////////////////
   //
   // 2. Blackbox Assertions
   //
   //////////////////////////////////////////////////////////////////////////////

   // ---------------------------------------------------------------------------      
   // f_conn_tick_drv: Check that tick follows tick_out of control_unit.
   //
   // This in san example. These kinds of connectivity checks are better done 
   // with formal connectivity checkers.
   // ---------------------------------------------------------------------------      
   
   property f_conn_tick_drv;
      @(posedge clk) disable iff (rst_n == '0)
	control_unit_1.tick_out == tick;
   endproperty
   
   af_conn_tick_drv: assert property(f_conn_tick_drv);
   
   
endmodule

`endif
