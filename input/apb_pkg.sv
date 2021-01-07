`include "audioport.svh"

package apb_pkg;

   // Address range of DUT
   
   localparam DUT_START_ADDRESS = 32'h8c000000;
   localparam DUT_END_ADDRESS =   32'h8c0003f8;
   
   // Address range of a wider APB bus section that includes the DUT's range.
   // Don't make the address space outside the DUT's range too large,
   // otherwise randomized addresses will not hit the DUT very often.
   
   localparam APB_START_ADDRESS = 32'h8bffff00;
   localparam APB_END_ADDRESS   = 32'h8c000400;
   
   // Number of wait states accepted before declaring a failed access.
   // Prevents slave from stopping the bus. Can be left as is.
   
   localparam APB_MAX_WAIT_STATES = 32;

   // Input delay of APB signal with respect to clock for clocking block.

`ifndef SYNTHESIS
   localparam realtime APB_INPUT_DELAY = 1000.0ps;
`endif
   
endpackage
   

