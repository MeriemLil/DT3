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

   // control_unitoutputs


   // dsp_unit outputs


   // cdc_unit outputs


   // i2s_unit outputs


   /////////////////////////////////////////////////////////////////////////////
   //
   // control_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
   control_unit control_unit_1
     (.clk(clk),
      .rst_n(rst_n)

      );

   /////////////////////////////////////////////////////////////////////////////
   //
   // dsp_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
 dsp_unit dsp_unit_1
   (
    .clk(clk),
    .rst_n(rst_n)
    
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
      .mrst_n(mrst_n)
      
      );

   /////////////////////////////////////////////////////////////////////////////
   //
   // i2s_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
   i2s_unit i2s_unit_1
     (
      .clk(mclk),
      .rst_n(mrst_n)

    );

endmodule


