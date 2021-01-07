`include "audioport.svh"

import audioport_pkg::*;

module dsp_unit(
		input logic clk,
		input logic rst_n,
		input logic tick_in,
		input logic cfg_in,
		input logic level_in,
		input logic clr_in,		
		input logic [1:0][23:0] abuf_in,
		input logic [DSP_REGISTERS-1:0][31:0] dsp_regs_in,
		input logic [31:0] level_reg_in,
		input logic [31:0] cfg_reg_in,
		output logic [1:0][23:0] dsp_out,
		output logic valid_out		
		);

   ////////////////////////////////////////////////////////////////////////////
   // Include SVA assertion module bindings here if testbench is in SystemC
   ////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_dsp_unit
`ifdef HLS_RTL
 `include "sva_bindings.svh"
`endif
`endif   

   ///////////////////////////////////////////////////////////////////////////
   //
   // Instantiation of 'dsp_unit_rtl' generated with HLS.
   // The module definition is in results/dsp_unit_hls_rtl.v.
   // Check the port definitions there.
   //
   ///////////////////////////////////////////////////////////////////////////
   
   /*    
    Tip: You can generate dsp_regs_in port mappings like this:
    
    main()
    {
    int i;
    for (i=0; i < 128; ++i)
    printf(".dsp_regs_in_%d(dsp_regs_in[%d]),\n", i, i);
    }
    
    Saved this code in portmap.c and compile with:
    cc -o portmap portmap.c
    Then run portmap and copy-paste the text here.   
    
    */   

   // To do: Remove comments from the folowing after you have run Stratus
   
     /*
   dsp_unit_rtl dsp_unit_rtl_1 
   (.clk(clk), 
    .rst_n(rst_n), 
    .abuf_in_0(abuf_in[0]),
    .abuf_in_1(abuf_in[1]), 
    .tick_in(tick_in),
    .cfg_in(cfg_in),
    .level_in(level_in),     
    .clr_in(clr_in),
    .cfg_reg_in(cfg_reg_in),
    .level_reg_in(level_reg_in),    
    .dsp_regs_in_0(dsp_regs_in[0]),
    .dsp_regs_in_1(dsp_regs_in[1]),

        // To do: Add port mappings

    .dsp_out_0(dsp_out[0]),
    .dsp_out_1(dsp_out[1])     
    );
*/

   
endmodule



