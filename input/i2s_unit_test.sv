//
//  i2s_unit.sv: test program for i2s_unit.
//
//

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program i2s_unit_test(
		      input logic 	  clk,
		      input logic 	  rst_n,
		      output logic 	  play_in,
		      output logic 	  tick_in,
		      output logic [23:0] audio_in_0,
		      output logic [23:0] audio_in_1,		      
		      output logic 	  cfg_in,
		      output logic [31:0] cfg_reg_in,
		      input logic 	  req_out,
		      input logic 	  ws_out,
		      input logic 	  sck_out,
		      input logic 	  sdo_out,
					  i2s_if i2s
		      );

   logic 			  tx_done = '0;
   logic 			  rx_done = '0;
   int 				  frame_number;
   logic [23:0] 		  LEFT_PATTERNS[FIFO_SIZE];
   logic [23:0] 		  RIGHT_PATTERNS[FIFO_SIZE];
   logic [1:0][23:0] 		  fifo[$];
   logic [1:0][23:0] 		  input_pattern;
   logic [1:0][23:0] 		  reference_pattern;      
   int 				  sample_counter;
   int 				  test_samples;
   int 				  random_delay;
   
   default clocking cb @(posedge clk);
      input sck_out, ws_out, sdo_out, req_out;
      output audio_in_0, audio_in_1, tick_in, play_in, cfg_in, cfg_reg_in;
   endclocking

   initial
     begin

	tick_in = '0;
	play_in = '0;
	cfg_in = '0;
	cfg_reg_in = '0;
	audio_in_0 = '0;
	audio_in_1 = '0;	      	      
	
	wait (rst_n);
	
	////////////////////////////////////////////////////////////////
	//
	// Transmitter side
	//
	////////////////////////////////////////////////////////////////

	fork
	   begin : data_generator
	      int 				  clock_divider;
	      logic [11:0] 			  counter;
	      
	      ///////////////////////////////////////////////////////////////////
	      //
	      // Test 1: Loop through valid rate values: 00, 01, 10 and 
	      // generate FIFO_SIZE samples.
	      //
	      ////////////////////////////////////////////////////////////////////

	      $info("T1: Directed");
	      
	      for (int rate = 0; rate < 3; ++rate)
		begin

		   // Initialize test variables
		   
		   sample_counter = 0;		   
		   frame_number = 0;
		   rx_done = '0;
		   test_samples = FIFO_SIZE;
		   fifo.delete();

		   // Configure sample rate
		   
		   ##16;		   
		   cb.cfg_reg_in <= 32'b11111111_00000000_00000000_00000000 + rate;	     
		   cb.cfg_in <= '1;	       
		   ##1;
		   cb.cfg_in <= '0;	       
		   ##1;

		   // Enable playback
		   cb.play_in <= '1;
		   ##1;
		   
		   // Sample generator loop
		   sample_counter = 0;
		   while (sample_counter < FIFO_SIZE)
		     begin
			if(cb.req_out)
			  begin
			     if (sample_counter == 0)
			       begin
				  input_pattern[0] = '1;
				  input_pattern[1] = '0;
			       end
			     else if (sample_counter == FIFO_SIZE-1)
			       begin
				  input_pattern[0] = '0;
				  input_pattern[1] = '1;
			       end
			     else
			       begin
				  input_pattern[0] = 24'hfff000;
				  input_pattern[1] = 24'hf0f0f0;
			       end
			     fifo.push_back(input_pattern);
			     cb.tick_in <= '1;
			     cb.audio_in_0 <= input_pattern[0];
			     cb.audio_in_1 <= input_pattern[1];
			     ++sample_counter;
			     ##1;
			     cb.tick_in <= '0;			     
			  end
			##1;
		     end

		   // Disable playback sometime during the last sample

		   case (rate)
		     0: 
		       ##(((FIFO_SIZE-1)*48+24)*MCLK_DIV_48000);
		     1: 
		       ##(((FIFO_SIZE-1)*48+24)*MCLK_DIV_96000);
		     2: 
		       ##(((FIFO_SIZE-1)*48+24)*MCLK_DIV_192000);
		   endcase // case (rate)
		   
		   cb.play_in <= '0;
		   ##1;

		   // Wait some time between tests
		   ##(2*2*24*MCLK_DIV_48000);
		end


	      ##100;
	      
	      ///////////////////////////////////////////////////////////////////
	      //
	      // Test 1: Loop through valid rate values: 00, 01, 10 and 
	      // generate many random samples (D)
	      //
	      ////////////////////////////////////////////////////////////////////

	      $info("T2: Random");

	      for (int rtest = 0; rtest < 64; ++rtest)
		begin
		   for (int rate = 0; rate < 3; ++rate)
		     begin

			// Initialize test variables
			
			sample_counter = 0;		   
			frame_number = 0;
			rx_done = '0;
			test_samples = FIFO_SIZE;
			fifo.delete();

			// Configure sample rate
			
			##16;		   
			cb.cfg_reg_in <= 32'b11111111_00000000_00000000_00000000 + rate;	     
			cb.cfg_in <= '1;	       
			##1;
			cb.cfg_in <= '0;	       
			##1;
			
			// Enable playback
			cb.play_in <= '1;
			##1;
			
			// Sample generator loop
			sample_counter = 0;
			while (sample_counter < 16)
			  begin
			     if(cb.req_out)
			       begin
				  input_pattern[0] = $urandom;
				  input_pattern[1] = $urandom;			
				  fifo.push_back(input_pattern);
				  cb.tick_in <= '1;
				  cb.audio_in_0 <= input_pattern[0];
				  cb.audio_in_1 <= input_pattern[1];
				  ++sample_counter;
				  ##1;
				  cb.tick_in <= '0;			     
			       end
			     ##1;
			  end

			// Disable playback sometime during the last sample

			case (rate)
			  0: 
			    random_delay = $urandom_range(0,24*MCLK_DIV_48000);
			  1:
			    random_delay = $urandom_range(0,24*MCLK_DIV_96000);
			  2:
			    random_delay = $urandom_range(0, 24*MCLK_DIV_192000);
			endcase // case (rate)

			##(random_delay);
			
			cb.play_in <= '0;
			##1;

			// Wait some time between tests
			##(2*2*24*MCLK_DIV_48000);
		     end

		end // for (int rtest = 0; rtest < 64; ++rtest)
	      
	      tx_done = '1;

	      #10us;
	      
	      $info("Test end");
	      
	   end : data_generator

	////////////////////////////////////////////////////////////////
	//
	// Receiver side
	//
	////////////////////////////////////////////////////////////////

	   begin : data_checker
	      logic tx_ok;
	      logic [1:0][23:0] audio;

	      while (!tx_done)
		begin 
		   i2s.monitor(tx_ok, audio);
		   reference_pattern = fifo.pop_front();
		   
		   test_T1T2: assert(audio[0] == reference_pattern[0] && audio[1] == reference_pattern[1])
			  else $error("tx error: left pattern: %h => %h right pattern: %h => %h", 
				      reference_pattern[0], audio[0], reference_pattern[1], audio[1]);
		   frame_number = frame_number + 1;
		   if (frame_number == test_samples) rx_done = '1;			     
		end

	   end : data_checker
	   
	join_any
	
     end
endprogram
