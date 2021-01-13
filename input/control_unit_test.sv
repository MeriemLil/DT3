`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program control_unit_test
  
  (input logic clk,
   input logic 			    rst_n,
				    apb_if apb,
				    irq_out_if irq,
   input logic [1:0][23:0] 	    abuf_out,
   input logic 			    cfg_out,
   input logic [31:0] 		    cfg_reg_out,
   input logic 			    level_out,
   input logic [31:0] 		    level_reg_out,
   input logic [DSP_REGISTERS-1:0][31:0] dsp_regs_out,
   input logic 			    clr_out, 
   input logic 			    tick_out,
   input logic 			    play_out,
   output logic 		    req_in
   );

   // These variables hold previous samples read from abuf_out in test T7
   logic [24:0] prev_left, prev_right;
   
   initial
     begin : test_program

	int 	        irq_counter;
	int 	        current_abuf;
	logic [1:0]   sample_rate;
	int 		test_number;
	int 		test_done;
	int 		test_status;
	int 		tests_passed;
	int 		tests_failed;
	int             all_tests_done;
	int 		sample_number;
	logic 		irq_out_state;
	logic         fail;
	logic [31:0]  addr;
	logic [31:0]  wdata;
	logic [31:0]  rdata;      

	irq_counter = 0;
	current_abuf = 0;
	sample_rate = RATE_48000;
	test_number = 0;
	test_done = 0;
	test_status = 0;
	tests_passed = 0;
	tests_failed = 0;
	all_tests_done = 0;
	sample_number = 1;
	prev_left = 0;
	prev_right = 0;
	
	// Wait for reset	
	req_in = '0;
	apb.reset; 

	#1us;
	
	fork

	   ////////////////////////////////////////////////////////////////
	   // APB SIDE
	   ////////////////////////////////////////////////////////////////

	   begin : apb_side
	      
	      fail = '0; // this is always ignored in the code below (too lazy...)

	      ////////////////////////////////////////////////////////////////
	      // Test 1: Write to CGF_REG
	      ////////////////////////////////////////////////////////////////

	      $info("T1 CFG_REG");
	      test_number = 1;
	      test_status = 1;
	      
	      addr = CFG_REG_APB_ADDRESS;
	      wdata = { 24'b00000000_0000000_00000000_000010, sample_rate};
	      apb.write(addr, wdata, fail);	 
	      apb.read(addr, rdata, fail);	     	     
	      test_T1: assert ((wdata == rdata) && (wdata == cfg_reg_out))
		else 
		  begin
		     $error("T1: CFG_REG write/read failure.");
		     test_status = 0;
		  end 
	      if (test_status == 1) ++tests_passed; else ++tests_failed;
	      
	      ////////////////////////////////////////////////////////////////
	      // Test 2: Write to LEVEL_REG
	      ////////////////////////////////////////////////////////////////
	      
	      $info("T2 LEVEL_REG");
	      test_number = 2;
	      test_status = 1;
	      
	      addr = LEVEL_REG_APB_ADDRESS;
	      wdata = { 24'b00000000_0000000_00000000_001110, sample_rate};
	      apb.write(addr, wdata, fail);	 
	      apb.read(addr, rdata, fail);	     	     
	      test_T2: assert ((wdata == rdata) && (wdata == level_reg_out))
		else 
		  begin
		     $error("T2: LEVEL_REG write/read failure.");
		     test_status = 0;
		  end 

	      if (test_status == 1) ++tests_passed; else ++tests_failed;
	      
	      ////////////////////////////////////////////////////////////////
	      // Test 3: Write to DSP_REGS
	      ////////////////////////////////////////////////////////////////
	      
	      $info("T3 DSP_REGS");
	      test_number = 3;
	      test_status = 1;

	      addr = DSP_REG_START_APB_ADDRESS;
	      wdata = { 24'b00000000_0000000_00000000_100010, sample_rate};
	      for (int i = addr; i < addr + DSP_REGISTERS; i = i + 4)
		 apb.write(i, wdata, fail);	 
	         apb.read(i, rdata, fail);	     	     
	         test_T3: assert ((wdata == rdata) && (wdata == dsp_regs_out))
		 else 
		  begin
		     $error("T3: DSP_REG write/read failure.");
		     test_status = 0;
		  end
	       end

	      if (test_status == 1) ++tests_passed; else ++tests_failed;

	      ////////////////////////////////////////////////////////////////
	      // Test 4: Fill audio buffer
	      ////////////////////////////////////////////////////////////////

	      $info("T4: ABUF");	
	      test_number = 4;
	      test_status = 1;
	      
	      addr = ABUF_START_APB_ADDRESS;
	      wdata = { 24'b00000000_0000000_00000000_000010, sample_rate};
	      for (int i = addr; i < addr + AUDIO_BUFFER_SIZE; i = i + 4)
		 apb.write(i, sample_number++, fail);	 
	         apb.read(i, rdata, fail);	     	     
	         test_T4: assert ((wdata == rdata) && (wdata == abuf_reg_out)) // abuf_reg_out?
		 else 
		  begin
		     $error("T4: ABUF_REG write/read failure.");
		     test_status = 0;
		  end 
	       end

	      if (test_status == 1) ++tests_passed; else ++tests_failed;
	      
	      ////////////////////////////////////////////////////////////////
	      // Test 5: Write CMD_CFG command.
	      ////////////////////////////////////////////////////////////////

	      $info("T5 CMD_CFG");	
	      test_number = 5;
	      test_done = 0;
	      
	      addr = CFG_REG_APB_ADDRESS;
	      wdata = CMD_CFG;
	      apb.write(addr, wdata, fail);	 
	      //apb.read(addr, rdata, fail);	     	     
	      

	      wait (test_done == 1);
	      
	      ////////////////////////////////////////////////////////////////
	      // Test 6: Write CMD_LEVEL command.
	      ////////////////////////////////////////////////////////////////

	      $info("T6 CMD_LEVEL");	
	      test_number = 6;
	      test_done = 0;
	      
	      addr = LEVEL_REG_APB_ADDRESS;
	      wdata = CMD_LEVEL;
	      apb.write(addr, wdata, fail);	 
	      //apb.read(addr, rdata, fail);	     	     
	      

	      wait (test_done == 1);
	      
	      ////////////////////////////////////////////////////////////////
	      // Test 7: Playback loop
	      ////////////////////////////////////////////////////////////////

	      $info("T7 begins");
	      test_number = 7;
	      test_done = 0;
	      
	      // To do: add APB write (command CMD_START to CMD_REG register)	      
	      addr = CMD_REG_APB_ADDRESS;
	      wdata = CMD_START;
	      apb.write(addr, wdata, fail);	 
	      //apb.read(addr, rdata, fail);

	      // ------------------------------------------------------------		

	      for(int t7 = 0; t7 < 3; ++t7)
		begin : SAMPLE_RATE_LOOP

		   ////////////////////////////////////////////////////////////////
		   // Test 7.1: Playback loop for one sample rate
		   ////////////////////////////////////////////////////////////////

		   $info("T7.1 (t7 = %d)", t7);	   
		   irq_counter = 0;

		   while (irq_counter < 3)
		     begin : INTERRUPT_LOOP

			////////////////////////////////////////////////////////////////
			// Wait for interrupt and fill next ABUF
			////////////////////////////////////////////////////////////////

			irq_out_state = '0;			

			// To do: Interrupt wait bypassed. Comment out when control_unit is done.
			@(posedge clk) irq_out_state = '1;			

			// To do: Interrupt wait. Remove from comments when control_unit is done.			
			// irq.monitor(irq_out_state);

			#(INTERRUPT_LATENCY);

			////////////////////////////////////////////////////////////////////////
			// P2 Fix! Comment the next out when the DUT is ready:
			// @(posedge clk) irq_out_state = '1;
			// Remember to put the comment back when the control_unit's RTL is ready.
			////////////////////////////////////////////////////////////////////////

			if (irq_out_state == '1)
			  begin

			     $info("T7.1.1: t7 = %d, irq_counter = %d", t7, irq_counter);
				

			     ////////////////////////////////////////////////////////////////
			     // Fill the ABUF that just got empty
			     ////////////////////////////////////////////////////////////////
			     ////////////////////////////////////////////////////////////////

			     // To do: Write 'sample_number' to ABUF0 or ABUF1 based on
			     //        'current_abuf' value (0 = ABUF0, 1 = ABUF1) and
			     //        increment 'sample_number' after each write.
			     if (current_abuf == '0)
				addr = ABUF0_START_APB_ADDRESS;
	      			wdata = { 24'b00000000_0000000_00000000_000010, sample_rate};
	      			for (int i = addr; i < addr + 2*AUDIO_BUFFER_SIZE; i = i + 4)
		 		    apb.write(i, sample_number++, fail);	 
	         		    apb.read(i, rdata, fail);	     	     
	         		    test_T7: assert ((wdata == rdata) && (wdata == abuf_reg_out)) //abuf_reg_out?
				    else 
		 		      begin
		    			 $error("T7.1.1: ABUF_REG write/read failure.");
		     			 test_status = 0;
		  		      end 
	     		        end
			     end
			     else
				addr = ABUF1_START_APB_ADDRESS;
	      			wdata = { 24'b00000000_0000000_00000000_000010, sample_rate};
	      			for (int i = addr; i < addr + 2*AUDIO_BUFFER_SIZE; i = i + 4)
		 		    apb.write(i, sample_number++, fail);	 
	         		    apb.read(i, rdata, fail);	     	     
	         		    test_T7: assert ((wdata == rdata) && (wdata == abuf_reg_out)) //abuf_reg_out?
				    else 
		 		      begin
		    			 $error("T7.1.1: ABUF_REG write/read failure.");
		     			 test_status = 0;
		  		      end 
	     		        end
			     end
	                     if (test_status == 1) ++tests_passed; else ++tests_failed;

			     // ------------------------------------------------------------				     
			     
			     ////////////////////////////////////////////////////////////////
			     // Swap buffer next time
			     ////////////////////////////////////////////////////////////////

			     if (current_abuf == 0)
			       current_abuf = 1;
			     else
			       current_abuf = 0;			 
			     irq_counter = irq_counter + 1;
			  end
		     end : INTERRUPT_LOOP
		   

		   ////////////////////////////////////////////////////////////////
		   // Test 7.2: Stop before sample rate change
		   ////////////////////////////////////////////////////////////////
		   
		   #10us;
		   $info("T7.2: CMD_STOP");
		   
		   // To do: Write CDM_STOP to CMD_REG register
		   addr = CMD_REG_APB_ADDRESS;
	      	   wdata = CMD_STOP;
	      	   apb.write(addr, wdata, fail);	 
	           //apb.read(addr, rdata, fail);

		   // -----------------------------------------		

		   ////////////////////////////////////////////////////////////////
		   // Test 7.3: Change sample rate
		   ////////////////////////////////////////////////////////////////

		   #25us;	   		   
		   case (sample_rate)
		     RATE_48000:
		       sample_rate = RATE_96000;
		     RATE_96000:
		       sample_rate = RATE_192000;
		     RATE_192000:
		       sample_rate = RATE_48000;
		   endcase

		   $info("T7.3: sample rate = %h", sample_rate);

		   // To do: Write sample rate code to CFG_REG
		   addr = CMD_REG_APB_ADDRESS;
	           wdata = sample_rate;
	           apb.write(addr, wdata, fail);	 
	           //apb.read(addr, rdata, fail);

		   
		   // -----------------------------------------		   	      		   

		   // To do: Write sample CMD_CFG command to CMD_REG register

		   addr = CMD_REG_APB_ADDRESS;
	      	   wdata = CMD_CFG;
	           apb.write(addr, wdata, fail);	 
	           //apb.read(addr, rdata, fail);
		   // -------------------------------------------------------
		   
		   ////////////////////////////////////////////////////////////////
		   // Test 7.4: Clear data paths
		   ////////////////////////////////////////////////////////////////

		   $info("T7.4: CMD_CLR");	     

		   current_abuf = 0;
		   sample_number = 1;
		   prev_left = 0;
		   prev_right = 0;

		   // To do: Write sample CMD_CLR command to CMD_REG register.
		   //        Then read all ABUF registers to make sure that they are zero.
		   
		   addr = CMD_REG_APB_ADDRESS;
	      	   wdata = CMD_CLR;
	           apb.write(addr, wdata, fail);	 
	           //apb.read(addr, rdata, fail);
		   // -------------------------------------------------------

		   
		   ////////////////////////////////////////////////////////////////
		   // Test 7.5: Fill audio buffer
		   ////////////////////////////////////////////////////////////////
		   
		   $info("T7.5: ABUF");	

		   // To do: Fill ABUF0 and ABUF1 completely with 'sample_number++'


	           test_status = 1;
	      
	           addr = ABUF_REG_APB_ADDRESS;
	           wdata = { 24'b00000000_0000000_00000000_000010, sample_rate};
	           for (int i = addr; i < addr + ABUF_REGISTERS; i = i + 4)
		 	apb.write(i, sample_number++, fail);	 
	         	apb.read(i, rdata, fail);	     	     
	         	test_T7.5: assert ((wdata == rdata) && (wdata == abuf_reg_out)) //abuf_reg_out?
		 	else 
		  	begin
		     	$error("T7.5: ABUF_REG write/read failure.");
		     	test_status = 0;
		  	end 
	       	   end

	      if (test_status == 1) ++tests_passed; else ++tests_failed;
		   
		   // -------------------------------------------------------				   
		   
		   ////////////////////////////////////////////////////////////////
		   // Test 7.6: Restart
		   ////////////////////////////////////////////////////////////////

		   $info("T7.6: CMD_START");	     	     

		   // To do: Write sample CMD_START command to CMD_REG register		   
		   
		   addr = CMD_REG_APB_ADDRESS;
	      	   wdata = CMD_START;
	           apb.write(addr, wdata, fail);	 
	           //apb.read(addr, rdata, fail);

		   // -------------------------------------------------------				   
		   
		   #10us;	     
		end : SAMPLE_RATE_LOOP
	      
	      #10us;	
      
	      ////////////////////////////////////////////////////////////////
	      // Test 8: Stop.
	      ////////////////////////////////////////////////////////////////

	      
	      $info("T8: CMD_STOP");	     	     	
	      test_number = 8;

	      // To do: Write sample CMD_STOP command to CMD_REG register
	      
	      addr = CMD_REG_APB_ADDRESS;
	      wdata = CMD_STOP;
	      apb.write(addr, wdata, fail);	 
	      //apb.read(addr, rdata, fail);
	      // --------------------------------------------------------
	      
	      #10us;


	      all_tests_done = 1;
	      
	   end : apb_side

	   ////////////////////////////////////////////////////////////////
	   // "DESIGN" SIDE
	   ////////////////////////////////////////////////////////////////
	   
	   begin : design_side

	      ////////////////////////////////////////////////////////////////
	      // Test 5: Write CMD_CFG command (read side)
	      ////////////////////////////////////////////////////////////////

	      wait (test_number == 5);
	      $info("Check T5");
	      
	      test_status = 0;

	      repeat(CMD_WAIT_STATES)
		begin
		   @(negedge clk)
		     begin
			if (cfg_out == '1)
			  begin
			     test_status = 1;
			     break;
			  end
		     end
		end

	      test_T5: assert(test_status == 1)
		else
		  begin
		     $error("T5: cfg_out pulse not detected");
		  end

	      if (test_status == 1) ++tests_passed; else ++tests_failed;
	      test_done = 1;
	      
	      ////////////////////////////////////////////////////////////////
	      // Test 6: Write CMD_LEVEL command (read side)
	      ////////////////////////////////////////////////////////////////

	      wait (test_number == 6);
	      $info("Check T6");
	      
	      test_status = 0;

	      repeat(CMD_WAIT_STATES)
		begin
		   @(negedge clk)
		     begin
			if (level_out == '1)
			  begin
			     test_status = 1;
			     break;
			  end
		     end
		end

	      test_T6: assert(test_status == 1)
		else
		  begin
		     $error("T6: level_out pulse not detected");
		  end

	      if (test_status == 1) ++tests_passed; else ++tests_failed;
	      test_done = 1;
	      
	      ///////////////////////////////////////////////////////////////////////
	      // Test 7: Playback loop (output read)
	      //         Assumption: abuf_out should prodice values (2,1), (3,4), ...
	      ///////////////////////////////////////////////////////////////////////
	      
	      wait (test_number == 7);
	      $info("Check T7");
	      test_status = 1;

	      fork

		 // abuf_our reader process
		 
		 begin : T7_abuf_out_reader
		    while(test_number == 7)
		      begin
			 @(negedge clk iff tick_out)
			   begin
			      if (prev_left != 0 && prev_right != 0)
				begin
				   test_T7: assert((abuf_out[0] == prev_left+2) && (abuf_out[1] == prev_right+2))
				     else
				       begin
					  $error("T7: abuf_out values wrong, actual (%d, %d), expected (%d, %d)",
						 abuf_out[0], abuf_out[1], prev_left+2, prev_right+2);
					  test_status = 0;				    
				       end
				end
			      prev_left = abuf_out[0];
			      prev_right = abuf_out[1];
			   end
		      end
		    
		 end : T7_abuf_out_reader		    

		 // req_in writer process
		 
		 begin : T7_req_writer
		    while(test_number == 7)
		      begin
			 int delay;
			 req_in <= '0;
			 case (sample_rate)
			   RATE_48000: delay = CLK_DIV_48000;
			   RATE_96000: delay =  CLK_DIV_96000;
			   RATE_192000: delay = CLK_DIV_192000;
			 endcase
			 repeat(delay)
			   @(posedge clk);
			 req_in <= '1;
			 @(posedge clk);			     
		      end
		    req_in = '0;
		 end : T7_req_writer

	      join_any

	      if (test_status == 1) ++tests_passed; else ++tests_failed;


	      wait (all_tests_done == 1);	      

	   end : design_side
	join_any

	$display("#####################################################################################################");	
	$display("control_unit_test results: PASSED: %d / FAILED: %d", tests_passed, tests_failed);
	$display("#####################################################################################################");	
	
	$finish;
	
     end : test_program
   
endprogram
