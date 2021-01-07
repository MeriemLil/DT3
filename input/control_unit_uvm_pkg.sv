`include "audioport.svh"

/////////////////////////////////////////////////////////
//
// control_unit_uvm_pkg
//
// This is a SystemVerilog package that defines the following classes
// control_unit_uvm_test
//
//    control_unit_agent
//    control_unit_env
//    control_unit_sequence
//    control_unit_uvm_test
//
/////////////////////////////////////////////////////////

package control_unit_uvm_pkg;

`ifndef SYNTHESIS   
   import audioport_pkg::*;
   import audioport_util_pkg::*;   
   import apb_uvm_pkg::*;
   import irq_agent_uvm_pkg::*;   

`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////////////////
//
// control_unit_agent
//
///////////////////////////////////////////////////////////

class control_unit_agent extends apb_agent;
   `uvm_component_utils(control_unit_agent)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     
   uvm_analysis_port #(apb_transaction) analysis_port;      
   uvm_analysis_imp #(irq_transaction, control_unit_agent) irq_analysis_export;
   uvm_event m_irq_event;
   
   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      irq_analysis_export = new("irq_analysis_export", this);
      analysis_port = new("analysis_port", this);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_irq_event = uvm_event_pool::get_global("irq_out");
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      m_monitor.analysis_port.connect(analysis_port);
   endfunction

   function void write(irq_transaction t);
      if(t.irq)
	m_irq_event.trigger();
   endfunction

endclass
   
///////////////////////////////////////////////////////////
//
// control_unit_env
//
///////////////////////////////////////////////////////////

class control_unit_env extends uvm_env;
   `uvm_component_utils(control_unit_env)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     
   control_unit_agent m_control_unit_agent;
   irq_agent m_irq_agent;

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_irq_agent = irq_agent::type_id::create("m_irq_agent", this);
      m_control_unit_agent = control_unit_agent::type_id::create("m_control_unit_agent", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      m_irq_agent.analysis_port.connect(m_control_unit_agent.irq_analysis_export);
   endfunction
   
endclass   


///////////////////////////////////////////////////////////
//
// control_unit_sequence
//
///////////////////////////////////////////////////////////


class control_unit_sequence extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(control_unit_sequence)

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
	
   function new (string name = "");
      super.new(name);
   endfunction
   
   task body;
      automatic int 	        counter = 0;
      automatic int 	        current_abuf = 0;
      automatic logic [1:0]   sample_rate = RATE_48000;
      automatic int 		test_number = 0;
      automatic int 		test_status = 0;
      automatic int 		tests_passed = 0;
      automatic int 		tests_failed = 0;
      automatic int 		sample_number = 1;
      apb_transaction write_tx;
      apb_transaction read_tx;      
      apb_sequencer tmp;
      uvm_event irq_event;

      irq_event = uvm_event_pool::get_global("irq_out");
      
      write_tx = apb_transaction::type_id::create("write_tx");
      read_tx = apb_transaction::type_id::create("read_tx");      

      #1us;
      
      ////////////////////////////////////////////////////////////////
      // Test 1: Write to CGF_REG
      ////////////////////////////////////////////////////////////////
      
      $info("T1 CFG_REG");
      test_number = 1;
      test_status = 1;
      
      write_tx.addr = CFG_REG_APB_ADDRESS;
      write_tx.data = { 24'b00000000_0000000_00000000, 6'b000010, sample_rate};
      write_tx.write_mode = '1;	      
      write_tx.fail = 0;
      start_item(write_tx);
      finish_item(write_tx);

      read_tx.addr = CFG_REG_APB_ADDRESS;
      read_tx.data = '0;
      read_tx.write_mode = '0;	      
      read_tx.fail = 0;
      start_item(read_tx);
      finish_item(read_tx);
      T1: assert (write_tx.data == read_tx.data)
	else 
	  begin
	     $error("T1: CFG_REG returned wrong data.");	     
	     test_status = 0;
	  end
      if (test_status == 1) ++tests_passed; else ++tests_failed;
      
      ////////////////////////////////////////////////////////////////
      // Test 2: Write to LEVEL_REG
      ////////////////////////////////////////////////////////////////
	
      $info("T2 LEVEL_REG");
      test_number = 2;
      test_status = 1;
      

      T2: assert (write_tx.data == read_tx.data)
	else 
	  begin
	     $error("T2: LEVEL_REG returned wrong data.");	     
	     test_status = 0;
	  end
      if (test_status == 1) ++tests_passed; else ++tests_failed;

      ////////////////////////////////////////////////////////////////
      // Test 3: Write to DSP_REGS
      ////////////////////////////////////////////////////////////////

      $info("T3 DSP_REGS");
      test_number = 3;
      test_status = 1;
      
      for(int unsigned i=0; i < DSP_REGISTERS; ++i)
	begin
	   write_tx.addr = DSP_REGS_START_APB_ADDRESS + i * 4;
	   write_tx.data = $urandom();
	   write_tx.data = write_tx.data;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);

	   read_tx.addr = DSP_REGS_START_APB_ADDRESS + i * 4;
	   read_tx.data = '0;
	   read_tx.write_mode = '0;	      
	   read_tx.fail = 0;
	   start_item(read_tx);
	   finish_item(read_tx);
	   T3: assert (write_tx.data == read_tx.data)
	     else 
	       begin
		  $error("T3: DSP_REGS region returned wrong data.");	     
		  test_status = 0;
	       end
	end
      if (test_status == 1) ++tests_passed; else ++tests_failed;
      
      ////////////////////////////////////////////////////////////////
      // T4: Fill audio buffer
      ////////////////////////////////////////////////////////////////
      

      ////////////////////////////////////////////////////////////////
      // Test 5: Write CMD_CFG command.
      ////////////////////////////////////////////////////////////////
      

      ////////////////////////////////////////////////////////////////
      // Test 6: Write CMD_LEVEL command.
      ////////////////////////////////////////////////////////////////
      

      ////////////////////////////////////////////////////////////////
      // Test 7: Playback loop
      ////////////////////////////////////////////////////////////////

      for(int t7 = 0; t7 < 4; ++t7)
	begin
	   
	   ////////////////////////////////////////////////////////////////
	   // Test 7.1: Playback loop for one sample rate
	   ////////////////////////////////////////////////////////////////

	   counter = 0;
	   
	   while(counter < 3)
	     begin

		////////////////////////////////////////////////////////////////
		// Wait for interrupt and fill next ABUF
		////////////////////////////////////////////////////////////////
		
		irq_event.wait_trigger();
		
		$info("T7.1.1: Interrupt %d", counter);
		#(INTERRUPT_LATENCY);

		////////////////////////////////////////////////////////////////
		// Fill the ABUF that just got empty
		////////////////////////////////////////////////////////////////
		

		////////////////////////////////////////////////////////////////
		// Swap buffer next time
		////////////////////////////////////////////////////////////////

		if (current_abuf == 0)
		  current_abuf = 1;
		else
		  current_abuf = 0;	
		counter = counter + 1;
	     end
	   
	   
	   ////////////////////////////////////////////////////////////////
	   // Test 7.2: Stop before sample rate change
	   ////////////////////////////////////////////////////////////////

	   #10us;	   
	   
	   ////////////////////////////////////////////////////////////////
	   // Test 7.3: Change sample rate
	   ////////////////////////////////////////////////////////////////

	   #30us;
	   
	   
	   ////////////////////////////////////////////////////////////////
	   // Test 7.4: Clear data paths
	   ////////////////////////////////////////////////////////////////
	   

	   ////////////////////////////////////////////////////////////////
	   // T7.5: Fill audio buffer
	   ////////////////////////////////////////////////////////////////
	   
	     
	   ////////////////////////////////////////////////////////////////
	   // Test 7.6: Play
	   ////////////////////////////////////////////////////////////////
	   

	   #10us;
	end
      
      #10us;      

      ////////////////////////////////////////////////////////////////
      // Test 8: Stop.
      ////////////////////////////////////////////////////////////////


      $display("#####################################################################################################");	
      $display("control_unit_sequence results: PASSED: %d / FAILED: %d", tests_passed, tests_failed);
      $display("#####################################################################################################");	
      
   endtask

   //----------------------------------------------------------------
   // Notice! This sequence can only access the control_unit's APB
   //         bus ports. Therefore the test program functions that need
   //         access to other ports are not implemented.
   //-----------------------------------------------------------------

endclass 

   
///////////////////////////////////////////////////////////
//
// control_unit_uvm_test
//
///////////////////////////////////////////////////////////
   
class control_unit_uvm_test extends uvm_test;
  `uvm_component_utils(control_unit_uvm_test)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
    
    control_unit_env m_env;

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
    
  function new(string name, uvm_component parent);
     super.new(name,parent);
  endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_env = control_unit_env::type_id::create("m_env", this);
  endfunction: build_phase

   task run_phase(uvm_phase phase);
      control_unit_sequence seq;
      seq = control_unit_sequence::type_id::create("seq");      
      phase.raise_objection(this); 
      seq.start( m_env.m_control_unit_agent.m_sequencer );
      phase.drop_objection(this); 
    endtask

endclass 
   
`endif //  `ifndef SYNTHESIS

   

endpackage
   

