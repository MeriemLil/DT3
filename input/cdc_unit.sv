`include "audioport.svh"

import audioport_pkg::*;

module cdc_unit(
		input logic 		 clk,
		input logic 		 rst_n,
		input logic [1:0][23:0]  dsp_in,
		input logic 		 play_in,
		input logic 		 tick_in,
		input logic 		 cfg_in,
		input logic [31:0] 	 cfg_reg_in,
		output logic 		 req_out,
		
		input logic 		 mclk,
		input logic 		 mrst_n,
		output logic [1:0][23:0] dsp_out, 
		output logic 		 play_out,
		output logic 		 tick_out,
		output logic 		 cfg_out,
		output logic [31:0] 	 cfg_reg_out,
		input logic 		 req_in		
		);

   
endmodule

/////////////////////////////////////////////////////////////////////////
// Module templates for synchronizers
/////////////////////////////////////////////////////////////////////////

module bit_sync
   (
    input logic clk,
    input logic rst_n,
    input logic data_in,
    output logic data_out);

   
endmodule

module pulse_sync
   (
    input logic clk,
    input logic rst_n,
    input logic data_in,
    output logic data_out);
   
endmodule


module handshaker #(DATABITS = 8) 
   (
    input logic clk1,
    input logic clk2,	      
    input logic rst1_n,
    input logic rst2_n,	      
    input logic enable1_in,
    input logic [DATABITS-1:0] data1_in,
    output logic enable2_out,
    output logic [DATABITS-1:0] data2_out    
    );

endmodule


	      
