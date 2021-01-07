`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program  dsp_unit_test(
		       input logic clk,
		       input logic rst_n,
		       output logic tick_in,
		       output logic cfg_in,
		       output logic level_in,
		       output logic clr_in,		
		       output logic [1:0][23:0] abuf_in,
		       output logic [DSP_REGISTERS-1:0][31:0] dsp_regs_in,
		       output logic [31:0] level_reg_in,
		       output logic [31:0] cfg_reg_in,
		       input logic [1:0][23:0] dsp_out
		       );

   logic [15:0]  level;
   real    c30[9] =
	   {
	    0.13579414601053794,   -0.13169583268492666,   -0.04549642672666201,   0.32821236511683544,   0.5318951755470149,   0.32821236511683544,   -0.045496426726662,   -0.13169583268492666,   0.13579414601053796
	    };
   
   real  c330[9] =
	 {
	  0.06757991089725654,   -0.05794125452513524,   -0.1517442802475166,   -0.2470965552575652,   0.7128561687460239,   -0.2470965552575652,   -0.15174428024751657,   -0.05794125452513524,   0.06757991089725657
	  };
   
   // To do: Declare a clocking block ---------------------------------------
   default clocking cb @(posedge clk);
      input 				       dsp_out;
      output 				       tick_in, cfg_in, level_in, clr_in, abuf_in, dsp_regs_in, cfg_reg_in, level_reg_in;
   endclocking 
   // ----------------------------------------------------------------------


      initial
     begin

	logic [4*FILTER_TAPS-1:0][31:0] filter_taps;
	if (read_filter_taps(filter_taps) == 0)
	  begin
	     $info("Using default filter coefficients.");
	  end
	
	// Initialize inputs directly before reset
	tick_in = '0;
	cfg_in = '0;
	level_in = '0;
	clr_in = '0;		
	abuf_in[0] = $urandom;
	abuf_in[1] = $urandom;	

	level_reg_in = '0;
	cfg_reg_in = '0;

	// Wait for rst_n to go high
	wait (rst_n);

	$info("T1: Program filter");

	##1;
	
	for (int i=0; i < 4*FILTER_TAPS; ++i)
	  begin
	     cb.dsp_regs_in[i] <= filter_taps[i];
	  end
	
	##1;
	cb.cfg_in <= '1;
	##1;
	cb.cfg_in <= '0;
	##10;

	$info("T2: Set level");

	level = 16'b1111111111111111;
	cb.level_reg_in <= { level, level };
	
	cb.level_in <= '1;
	##1;
	cb.level_in <= '0;	
	##10;

	$info("T3: One 192kHz sample, filter enabled");	

	cb.cfg_reg_in <= 32'b00000000_00000000_00000000_00001010;
	cb.cfg_in <= '1;
	##1;
	cb.cfg_in <= '0;
	##10;

	abuf_in[0] = $urandom;
	abuf_in[1] = $urandom;	
	cb.tick_in <= '1;
	##1;
	cb.tick_in <= '0;
	##(CLK_DIV_192000);
	##10;

	$info("T4: One 192kHz sample, filter disabled");		
	
	cb.cfg_reg_in <= 32'b00000000_00000000_00000000_00000010;
	cb.cfg_in <= '1;
	##1;
	cb.cfg_in <= '0;
	##10;
	
	abuf_in[0] = $urandom;
	abuf_in[1] = $urandom;	
	cb.tick_in <= '1;
	##1;
	cb.tick_in <= '0;
	##(CLK_DIV_192000);
	##10;


	$info("T5: One 192kHz sample, filter enabled, cfg_in during processing");	

	cb.cfg_reg_in <= 32'b00000000_00000000_00000000_00001010;
	cb.cfg_in <= '1;
	##1;
	cb.cfg_in <= '0;
	##10;
	
	cb.tick_in <= '1;
	##1;
	cb.tick_in <= '0;
	##2;
	cb.cfg_in <= '1;
	##1;
	cb.cfg_in <= '0;
	##(CLK_DIV_192000);	
	##10;

	$info("T6: One 192kHz sample, filter enabled, cfg_in, clr_in, level_in during processing");	

	cb.cfg_reg_in <= 32'b00000000_00000000_00000000_00001010;
	cb.cfg_in <= '1;
	##1;
	cb.cfg_in <= '0;
	##10;
	
	cb.tick_in <= '1;
	##1;
	cb.tick_in <= '0;
	##2;
	cb.cfg_in <= '1;
	##1;
	cb.cfg_in <= '0;
	##1;
	cb.level_in <= '1;
	##1;
	cb.level_in <= '0;
	##1;
	cb.clr_in <= '1;
	##1;
	cb.clr_in <= '0;
	##(CLK_DIV_192000);	
	##10;
	

	$info("T7: Clear audio data");
	
	cb.clr_in <= '1;
	##1;
	cb.clr_in <= '0;	

	##10;

	$info("T8: Continuous play, filter enabled, level changes");
	
	cb.cfg_reg_in <= 32'b00000000_00000000_00000000_00001010;
	cb.cfg_in <= '1;
	##1;
	cb.cfg_in <= '0;
	##10;

	abuf_in[0] = 2**22-1;
	abuf_in[1] = -2**21-1;
	for (int i = 0; i < 480; ++i) 
	  begin

	     if (i % 400 == 0)
	       abuf_in[0] = -abuf_in[0];
	     if (i % 200 == 0)
	       abuf_in[1] = -abuf_in[1];

	     cb.tick_in <= '1;
	     ##1;
	     cb.tick_in <= '0;
	     ##(CLK_DIV_192000/20);	     
	     level = level - 2;
	     cb.level_reg_in <= { level, level };
	     cb.level_in <= '1;
	     ##1;
	     cb.level_in <= '0;	
	     ##(CLK_DIV_192000 - CLK_DIV_192000/20 -1);		     
	  end 

	##10;

	$finish;
	
     end

endprogram
   
