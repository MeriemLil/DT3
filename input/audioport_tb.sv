
`ifndef SYNTHESIS

//`define UVM_TESTBENCH 1

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

`ifdef UVM_TESTBENCH
`include "uvm_macros.svh"
import uvm_pkg::*;
import apb_uvm_pkg::*;
import irq_agent_uvm_pkg::*;
import control_unit_uvm_pkg::*;
import audioport_uvm_pkg::*;
`endif

module audioport_tb  #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic clk;
   logic mclk;
   logic rst_n;
   logic mrst_n;
   logic  psel_in;
   logic  penable_in;
   logic  pwrite_in;
   logic [31:0]  paddr_in;
   logic [31:0] pwdata_in;
   logic [31:0] prdata_out;
   logic 	pready_out;
   logic 	pslverr_out;
   logic irq_out;
   logic ws_out;
   logic sck_out;   
   logic sdo_out;
   logic test_mode_sel;
   logic [31:0] ref_prdata_out;
   logic 	ref_pready_out;
   logic 	ref_pslverr_out;
   logic ref_irq_out;
   logic ref_ws_out;
   logic ref_sck_out;   
   logic ref_sdo_out;
   logic stop_clocks;
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Interface object declarations and connections
   //
   ////////////////////////////////////////////////////////////////////////////

   apb_if apb(clk, rst_n);   
   irq_out_if irq(clk, rst_n);   
   i2s_if i2s(mclk, mrst_n);
   assign psel_in = apb.psel;
   assign penable_in = apb.penable;   
   assign pwrite_in = apb.pwrite;
   assign paddr_in = apb.paddr;
   assign pwdata_in = apb.pwdata;
   assign apb.prdata = prdata_out;
   assign apb.pready = pready_out;
   assign apb.pslverr = pslverr_out;
   assign irq.irq_out = irq_out;
   assign i2s.sdo = sdo_out;
   assign i2s.sck = sck_out;
   assign i2s.ws  = ws_out;

   ////////////////////////////////////////////////////////////////////////////
   //
   // Clock and reset generation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	clk = '0;
	forever begin
	   if (stop_clocks == '1) break;
	   #(CLK_PERIOD/2) clk = ~clk;
	end
     end

   initial
     begin
	realtime delay;
	mclk = '0;
	delay = real'($urandom_range(0, MCLK_PERIOD/2))/10.0;
	#(delay);
	forever begin
	   if (stop_clocks == '1) break;
	   #(MCLK_PERIOD/2) mclk = ~mclk;
	end
     end
   
   initial
     begin
	rst_n = '0;
	@(negedge clk) rst_n = '0;
	@(negedge clk) rst_n = '1;	
     end

      initial
     begin
	mrst_n = '0;
	@(negedge mclk) mrst_n = '0;
	@(negedge mclk) mrst_n = '1;	
     end

   ////////////////////////////////////////////////////////////////////////////
   //
   // DUT instantiation
   //
   ////////////////////////////////////////////////////////////////////////////

   audioport DUT_INSTANCE
     (.*
      );

   ////////////////////////////////////////////////////////////////////////////
   //
   // Include SVA assertion module bindings
   //
   ////////////////////////////////////////////////////////////////////////////

 `include "sva_bindings.svh"

   ////////////////////////////////////////////////////////////////////////////
   //
   // Test program instantiation for non-UVM test
   //
   ////////////////////////////////////////////////////////////////////////////
   
`ifndef UVM_TESTBENCH

   audioport_test TEST (.*);
   
`else

   ////////////////////////////////////////////////////////////////////////////
   //
   // UVM test setup
   //
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	stop_clocks = '0;
	test_mode_sel = '0; // disable test mode for all UVM tests
	save_test_parameters("reports/3_vsim_audioport_test_parameters.txt");	
	uvm_top.finish_on_completion = 1;
	uvm_config_db #(int)::set( null , "" , "APB_TEST_CYCLES" , 200);
	uvm_config_db #(virtual interface apb_if)::set( null , "" , "apb_if_config" , apb);
        uvm_config_db #(virtual interface irq_out_if)::set( null , "" , "irq_out_if_config" , irq);
        uvm_config_db #(virtual interface i2s_if)::set( null , "" , "i2s_if_config" , i2s);      
   	run_test();
        stop_clocks = '1;
        $finish;
   
     end

`endif // !`ifndef UVM_TESTBENCH
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Reference model instantiation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL      

	    audioport REF_INSTANCE
	      (
	       .prdata_out(ref_prdata_out),
	       .pready_out(ref_pready_out),
	       .pslverr_out(ref_pslverr_out),
	       .irq_out(ref_irq_out),
	       .sck_out(ref_sck_out),
	       .ws_out(ref_ws_out),
	       .sdo_out(ref_sdo_out),
	       .*
	       );

	 //////////////////////////////////////
         // Comparison code begin
	 //////////////////////////////////////
	 
	 // clk clock domain output

	 // mclk clock domain outputs
	 
	 //////////////////////////////////////
	 // Comparison code end
	 //////////////////////////////////////
	 
      end 
   endgenerate


   initial
     begin
	save_test_parameters("reports/3_vsim_audioport_test_parameters.txt");	
     end

endmodule 

`endif
