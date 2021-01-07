//
//  cdc_unit.sv: test program for cdc_unit.
//

`define TEST_LOOPS 2000

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program cdc_unit_test(
		input logic 		 clk,
		input logic 		 rst_n,
		output logic [1:0][23:0] dsp_in, 
		output logic 		 play_in,
		output logic 		 tick_in, 
		output logic 		 cfg_in,
		output logic [31:0] 	 cfg_reg_in,
		input logic 		 req_out,
		      
		input logic 		 mclk,
		input logic 		 mrst_n,
		input logic [1:0][23:0]  dsp_out, 
		input logic 		 play_out,
		input logic 		 tick_out,
		input logic 		 cfg_out,
		input logic [31:0] 	 cfg_reg_out,
		output logic 		 req_in
		);

   initial
     begin
	logic [31:0] cfg_reg;
	logic [1:0][23:0] dsp;
	const int 	  WAIT_TIME = 100;
	int 		  wait_counter;
	logic 		  play_out_seen;
	logic 		  req_out_seen;	
	int 		  test_number;
	int 		  test_done;
	int 		  test_status;
	int 		  tests_passed;
	int 		  tests_failed;
	int 		  all_tests_done;
	realtime 	  delay;
	
	play_in = '0;
	tick_in = '0;
	cfg_in = '0;
	cfg_reg_in = $urandom;
	dsp_in[0] = $urandom;
	dsp_in[1] = $urandom;	
	req_in = '0;
	test_number = 0;
	
	fork
	   begin : clk_side
	      while(rst_n == '0)
		@(negedge clk);

	      //////////////////////////////////////////////////////////////////////////7
	      // T1: cfg_in / cfg_reg_in test
	      //////////////////////////////////////////////////////////////////////////7

	      repeat(20)
		@(negedge clk);

	      $info("T1 cfg_in/cfg_reg_in");
	      test_number = 1;
	      test_status = 1;

	      @(negedge clk);
	      
	      repeat(`TEST_LOOPS)
		begin
		   // Input random cfg_in value
		   cfg_reg = $urandom;
		   cfg_reg_in = cfg_reg;
			cfg_in ='1;
		   @(negedge clk);
		   cfg_in ='0;
		   cfg_reg_in = '0;
		   repeat (CDC_HANDSHAKER_INTERVAL-1)
		     @(negedge clk);
		end // repeat (`TEST_LOOPS)

	      //////////////////////////////////////////////////////////////////////////7
	      // T2: tick_in / dsp_in test
	      //////////////////////////////////////////////////////////////////////////7

	      repeat(20)
		@(negedge clk);
	      
	      $info("T2: tick_in/dsp_in");	
	      test_number = 2;
	      test_status = 1;
	      
	      repeat(`TEST_LOOPS)
		begin
		   // Input random audio samples
		   dsp[0] = $urandom;
		   dsp[1] = $urandom;	
		   dsp_in[0] = dsp[0];
		   dsp_in[1] = dsp[1];
		   
		   tick_in ='1;
		   @(negedge clk);
		   tick_in ='0;
		   dsp_in[0] = '0;
		   dsp_in[1] = '0;

		   repeat (CDC_HANDSHAKER_INTERVAL)
		     @(negedge clk);
		end

	      //////////////////////////////////////////////////////////////////////////7
	      // T3: play_in
	      //////////////////////////////////////////////////////////////////////////7

	      repeat(20)
		@(negedge clk);

	      $info("T3: play_in");
	      test_number = 3;
	      test_status = 1;

	      repeat (`TEST_LOOPS)
		begin
		   play_in = '1;

		   repeat(CDC_BITSYNC_INTERVAL)
		     @(negedge clk);	
		   
		   play_in = '0;

		   repeat(CDC_BITSYNC_INTERVAL)
		     @(negedge clk);	
		end

	      if (test_status == 1) ++tests_passed; else ++tests_failed;
	      
	      //////////////////////////////////////////////////////////////////////////7
	      // T4: req_in
	      //////////////////////////////////////////////////////////////////////////7

	      repeat(20)
		@(negedge clk);

	      $info("T4: req_in");
	      
	      test_number = 4;
	      test_status = 1;
	      
	      while (test_number == 4)
		begin
		   @(negedge clk);		   
		end

	   end : clk_side


	   
	   begin : mclk_side

	      //////////////////////////////////////////////////////////////////////////7
	      // T1: cfg_in / cfg_reg_in test
	      //////////////////////////////////////////////////////////////////////////7
	      
	      wait (test_number == 1);

	      while (test_number == 1)
		begin
		   @(posedge mclk);
		   if (cfg_out)
		     begin
			test_T1: assert (cfg_reg == cfg_reg_out)
			  else begin
			     test_status = 0;
			     $error("cfg_reg_in != cfg_reg_out");
			  end
		     end
		end

	      if (test_status == 1) ++tests_passed; else ++tests_failed;
	      
	      //////////////////////////////////////////////////////////////////////////7
	      // T2: tick_in / dsp_in test
	      //////////////////////////////////////////////////////////////////////////7
	      
	      wait (test_number == 2);
	      
	      while (test_number == 2)
		begin
		   @(posedge mclk);
		   if (tick_out)
		     begin
			test_T2L: assert (dsp[0] == dsp_out[0])
			  else begin
			     test_status = 0;
			     $error("T2L: dsp_in[0] != dsp_out[0]");	       
			  end
			test_T2R: assert (dsp[1] == dsp_out[1])
			  else begin
			    test_status = 0;
			     $error("T2R: dsp_in[1] != dsp_out[1]");
			  end
		     end
		end

	      if (test_status == 1) ++tests_passed; else ++tests_failed;
	      
	      //////////////////////////////////////////////////////////////////////////7
	      // T3: play_in
	      //////////////////////////////////////////////////////////////////////////7
	      
	      wait (test_number == 3);
	      
	      while(test_number == 3)
		begin
		   @(negedge mclk);		   
		end


	      //////////////////////////////////////////////////////////////////////////7
	      // T4: req_in
	      //////////////////////////////////////////////////////////////////////////7

	      wait (test_number == 4);	      
	      repeat(5)
		@(negedge mclk);

	      repeat(`TEST_LOOPS)
		begin
		   req_out_seen = '0;
		   req_in = '1;
		   @(negedge mclk);	
		   req_in = '0;

		   repeat(CDC_PULSESYNC_INTERVAL)
		     @(negedge mclk);	

		end

	      if (test_status == 1) ++tests_passed; else ++tests_failed;
	      
	      test_number = 0; // this will end 'clk_side'
	      
	   end : mclk_side

	join_any

	$display("#####################################################################################################");	
	$display("cdc_unit_test results: PASSED: %d / FAILED: %d", tests_passed, tests_failed);
	$display("#####################################################################################################");	
	
     end

   
   
endprogram
