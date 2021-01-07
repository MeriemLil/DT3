//
//  audioport.sv: Top-level module of audioport design.
//

`include "audioport.svh"

import audioport_pkg::*;

module audioport
  
  (input logic clk,
   input logic rst_n,
   input logic mclk,
   input logic mrst_n,

   // APB interface
   
   input logic  psel_in,
   input logic  penable_in,
   input logic  pwrite_in,
   input logic [31:0]  paddr_in,
   input logic [31:0] pwdata_in,
   output logic [31:0] prdata_out,
   output logic pready_out,
   output logic pslverr_out,

   // Interrupt request
   //    
   output logic irq_out,
   
   // Audio outputs

   output logic ws_out,
   output logic sck_out,   
   output logic sdo_out,

   // Test mode select (scan enable)
   input logic test_mode_sel
   );


   /////////////////////////////////////////////////////////////////////////////
   //
   // Internal signal variables
   //
   /////////////////////////////////////////////////////////////////////////////

   // control_unit outputs
   logic [31:0] cfg_reg;
   logic [DSP_REGISTERS-1:0][31:0] dsp_regs;
   logic [31:0] level_reg;
   logic [1:0][23:0] abuf;
   logic clr;
   logic level;
   logic cfg;
   logic tick;
   logic play;
   logic req;

   // dsp_unit outputs
   logic [1:0][23:0] dsp;
   logic dsp_tick;

   // cdc_unit outputs
   logic [31:0] mcfg_reg;
   logic [1:0][23:0] mdsp;
   logic mtick;
   logic mcfg;
   logic mplay;
   logic mreq;

   // i2s_unit outputs


   /////////////////////////////////////////////////////////////////////////////
   //
   // control_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
   control_unit control_unit_1
     (.clk(clk),
      .rst_n(rst_n),
      .pready_out(pready_out),
      .psel_in(psel_in),
      .penable_in(penable_in),
      .pwrite_in(pwrite_in),
      .paddr_in(paddr_in),
      .pwdata_in(pwdata_in),
      .prdata_out(prdata_out),
      .pslverr_out(pslverr_out),
      .irq_out(irq_out),
      .cfg_reg_out(cfg_reg),
      .dsp_regs_out(dsp_regs),
      .level_reg_out(level_reg),
      .abuf_out(abuf),
      .clr_out(clr),
      .level_out(level),
      .cfg_out(cfg),
      .tick_out(tick),
      .play_out(play),
      .req_in(req)
      );

   /////////////////////////////////////////////////////////////////////////////
   //
   // dsp_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
 dsp_unit dsp_unit_1
   (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_reg_in(cfg_reg),
    .dsp_regs_in(dsp_regs),
    .level_reg_in(level_reg),
    .abuf_in(abuf),
    .clr_in(clr),
    .level_in(level),
    .cfg_in(cfg),
    .tick_in(tick),
    .dsp_out(dsp),
    .valid_out(dsp_tick)    
    );

   /////////////////////////////////////////////////////////////////////////////
   //
   // cdc_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
   cdc_unit cdc_unit_1 
     (
      .clk(clk),
      .rst_n(rst_n),
      .mclk(mclk),
      .mrst_n(mrst_n),
      .cfg_reg_in(cfg_reg),
      .dsp_in(dsp),
      .tick_in(dsp_tick),
      .cfg_in(cfg),
      .play_in(play),
      .req_out(req),
      .cfg_reg_out(mcfg_reg),
      .dsp_out(mdsp),
      .tick_out(mtick),
      .cfg_out(mcfg),
      .play_out(mplay),
      .req_in(mreq)
      );

   /////////////////////////////////////////////////////////////////////////////
   //
   // i2s_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
   i2s_unit i2s_unit_1
     (
      .clk(mclk),
      .rst_n(mrst_n),
      .cfg_reg_in(mcfg_reg),
      .audio_in_0(mdsp[0]),
      .audio_in_1(mdsp[1]),
      .tick_in(mtick),
      .cfg_in(mcfg),
      .play_in(mplay),
      .req_out(mreq),
      .ws_out(ws_out),
      .sck_out(sck_out),
      .sdo_out(sdo_out)
    );

endmodule


