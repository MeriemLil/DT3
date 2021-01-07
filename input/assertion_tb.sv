// assertion_tb.sv: Simple testbench for debugging assertions 
//
// Usage:
//      1. Create a scenario where an assertion a_X based on property X should
//         PASS and FAIL in the initial proceudre below
//      2. Run the script to verify that the waveforms look OK
//         vsim -do scripts/assertion_tb.tcl
//      3. Declare the property and assertions below the initial process
//      4. Run the script again. The script puts all assertions in the Wave window.
//         Expand an assertion (+) and its ActiveCount (+) to view evaluation details
//      5. To get a detailed view of assertion evaluation, do the following:
//         a) Activate the Assertions tab
//         b) Select an assertion
//         c) Using the right button, execure View ATV.. and select a specific
//            passing or failure of the assertion (ATV = assertion thread view)
//         d) You can now follow the evaluation of property expressions in time
// 

import audioport_pkg::*;

module assertion_tb; 
   
   // Clock and reset 
   logic clk = '0, rst_n = 0; 
   always #10ns clk = ~clk; 
   initial @(negedge clk) rst_n = '1; 

   logic psel_in;
   logic penable_in;
   logic pwrite_in;
   logic [31:0]  paddr_in;
   logic [31:0] pwdata_in;
   logic [31:0] prdata_out;
   logic pready_out;
   logic pslverr_out;
   logic irq_out;
   logic [1:0][23:0] abuf_out;
   logic cfg_out;
   logic [31:0] cfg_reg_out;
   logic level_out;
   logic [31:0] level_reg_out;
   logic [DSP_REGS-1:0][31:0] dsp_regs_out;
   logic clr_out;    
   logic tick_out;
   
   ///////////////////////////////////////////////////////////////////
   // Test data generation process 
   ///////////////////////////////////////////////////////////////////

   initial 
     begin

	
	$info("a_cfg_reg_write OK");
	psel_in = '0;
	penable_in = '0;
	pwrite_in = '0;
	pready_out = '0;
	paddr_in = CFG_REG_APB_ADDRESS;
	pwdata_in = $urandom;
	cfg_reg_out = '0;
	@(negedge clk); 
	psel_in = '1;
	pwrite_in = '1;
	pready_out = '1;
	@(negedge clk); 	
	penable_in = '1;
	@(negedge clk); 	
	psel_in = '0;
	penable_in = '0;
	pwrite_in = '0;
	pready_out = '0;
	cfg_reg_out = pwdata_in;
	@(negedge clk);

	#1us;
	
	$info("a_cfg_reg_write FAIL1");
	psel_in = '0;
	penable_in = '0;
	pwrite_in = '0;
	pready_out = '0;
	paddr_in = CFG_REG_APB_ADDRESS;
	pwdata_in = $urandom;
	@(negedge clk); 
	psel_in = '1;
	pwrite_in = '1;
	pready_out = '1;
	@(negedge clk); 	
	penable_in = '1;
	@(negedge clk); 	
	psel_in = '0;
	penable_in = '0;
	pwrite_in = '0;
	pready_out = '0;
	@(negedge clk); // One cycle too late	
	cfg_reg_out = pwdata_in;
	@(negedge clk);

	
	#1us;
	
	$info("a_cfg_reg_write FAIL2");
	psel_in = '0;
	penable_in = '0;
	pwrite_in = '0;
	pready_out = '0;
	paddr_in = CFG_REG_APB_ADDRESS;
	pwdata_in = $urandom;
	@(negedge clk); 
	psel_in = '1;
	pwrite_in = '1;
	pready_out = '1;
	@(negedge clk); 	
	penable_in = '1;
	@(negedge clk); 	
	psel_in = '0;
	penable_in = '0;
	pwrite_in = '0;
	pready_out = '0;
	cfg_reg_out = pwdata_in ^ 32'h00000001; // Wrong data
	@(negedge clk);

	#1us;
	
	$finish;
	
     end 
   
   ///////////////////////////////////////////////////////////////////
   // Properties and assertions
   ///////////////////////////////////////////////////////////////////

   
   // ---------------------------------------------------------------------------      
   // cfg_reg_write
   // ---------------------------------------------------------------------------

   property cfg_reg_write;
      @(posedge clk) disable iff (rst_n == '0)
        psel_in && penable_in && pready_out && pwrite_in && (paddr_in == CFG_REG_APB_ADDRESS) |=> cfg_reg_out == $past(pwdata_in);
   endproperty
      
   a_cfg_reg_write: assert property(cfg_reg_write)
     else $error("cfg_reg_out value differs from value written to CFG_REG");
   c_cfg_reg_write: cover property(cfg_reg_write);
      
endmodule 
