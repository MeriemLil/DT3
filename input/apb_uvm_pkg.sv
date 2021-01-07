
package apb_uvm_pkg;

`ifndef SYNTHESIS
   
/////////////////////////////////////////////////////////
//
// apb_uvm_pkg
//
// This is a SystemVerilog package that defines the following classes
// for the APB testbench example.
//
//    apb_transaction
//    apb_driver
//    apb_monitor
//    apb_analyzer
//    apb_sequencer
//    apb_sequence_config
//    apb_sequence
//    apb_agent
//    apb_env
//    apb_test
//
/////////////////////////////////////////////////////////

`include "uvm_macros.svh"

   import uvm_pkg::*;
   import apb_pkg::*;
   
///////////////////////////////////////////////////////////
//
// Class: apb_transaction
//
///////////////////////////////////////////////////////////

class apb_transaction extends uvm_sequence_item;
   `uvm_object_utils(apb_transaction)
  
   rand logic [31:0] addr;
   rand logic [31:0] data;
   rand logic write_mode;
   logic fail;
   
   function new (string name = "");
      super.new(name);
   endfunction
   
   constraint c_addr { addr >= APB_START_ADDRESS; addr < APB_END_ADDRESS; }

   function void do_copy(uvm_object rhs);
      apb_transaction rhs_;
      if(!$cast(rhs_, rhs)) begin
	 uvm_report_error("apb_transaction.do_copy:", "Cast failed");
	 return;
      end

      super.do_copy(rhs); 
      addr = rhs_.addr;
      data = rhs_.data;
      write_mode = rhs_.write_mode;
      fail = rhs_.fail;
      
   endfunction


  function void do_record(uvm_recorder recorder);
   super.do_record(recorder);
   `uvm_record_attribute(recorder.tr_handle, "addr", addr);
   `uvm_record_attribute(recorder.tr_handle, "data", data);
   `uvm_record_attribute(recorder.tr_handle, "write_mode", write_mode);
   `uvm_record_attribute(recorder.tr_handle, "fail", fail);      
   endfunction

endclass: apb_transaction


///////////////////////////////////////////////////////////
//
// Class: apb_driver
//
///////////////////////////////////////////////////////////

class apb_driver extends uvm_driver #(apb_transaction);
   `uvm_component_utils(apb_driver)

   virtual apb_if m_apb_if;

   int m_writes_to_dut = 0;
   int m_reads_from_dut = 0;   
   int m_writes_to_other = 0;
   int m_reads_from_other = 0;   
   int m_failed_writes_to_dut = 0;
   int m_failed_reads_from_dut = 0;   
   int m_failed_writes_to_other = 0;
   int m_failed_reads_from_other = 0;   
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      if (!uvm_config_db #(virtual interface apb_if)::get(this, "", "apb_if_config", m_apb_if))
	begin
	   `uvm_error("apb_driver config error" , "uvm_config_db #( virtual interface apb_if )::get cannot find resource apb_if" );
	end   
   endfunction
   
   task run_phase(uvm_phase phase);

      m_apb_if.reset();

      forever
	begin
	   apb_transaction tx;
	   int wait_counter;
	   
	   seq_item_port.get_next_item(tx);

	   if (tx.write_mode == '1)
	     begin
		m_apb_if.write(tx.addr, tx.data, tx.fail);
		if (tx.addr >= DUT_START_ADDRESS && tx.addr <= DUT_END_ADDRESS)
		  begin
		     ++m_writes_to_dut;
		     if (tx.fail == '1)
		       ++m_failed_writes_to_dut;
		  end
		else
		  begin
		     ++m_writes_to_other;
		     if (tx.fail == '1)
		       ++m_failed_writes_to_other;
		  end
	     end
	   else
	     begin
		m_apb_if.read(tx.addr, tx.data, tx.fail);

		if (tx.addr >= DUT_START_ADDRESS && tx.addr <= DUT_END_ADDRESS)
		  begin
		     ++m_reads_from_dut;
		     if (tx.fail == '1)
		       ++m_failed_reads_from_dut;
		  end
		else
		  begin
		     ++m_reads_from_other;
		     if (tx.fail == '1)
		       ++m_failed_reads_from_other;
		  end
	     end

	   seq_item_port.item_done();

	end
   endtask

   function void report_phase( uvm_phase phase );
      uvm_report_info("apb_driver", $sformatf("DUT:       %6d writes, %6d reads generated", m_writes_to_dut, m_reads_from_dut));
      uvm_report_info("apb_driver", $sformatf("           %6d failed, %6d failed", m_failed_writes_to_dut, m_failed_reads_from_dut));      
      uvm_report_info("apb_driver", $sformatf("Other APB: %6d writes, %6d reads generated", m_writes_to_other, m_reads_from_other));      
      uvm_report_info("apb_driver", $sformatf("           %6d failed, %6d failed", m_failed_writes_to_other, m_failed_reads_from_other));      
   endfunction
   
endclass



///////////////////////////////////////////////////////////
//
// Class: apb_monitor
//
///////////////////////////////////////////////////////////

class apb_monitor extends uvm_monitor;
   `uvm_component_utils(apb_monitor)

   uvm_analysis_port #(apb_transaction) analysis_port;
   
   virtual apb_if m_apb_if;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      analysis_port = new("analysis_port", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      if (!uvm_config_db #(virtual interface apb_if)::get(this, "", "apb_if_config", m_apb_if))
	begin
	   `uvm_error("apb_monitor config error" , "uvm_config_db #( virtual interface apb_if )::get cannot find resource apb_if" );
	end

   endfunction

   task run_phase(uvm_phase phase);
      logic tx_ok;
      
      apb_transaction tx, tx_clone;      
      tx = apb_transaction::type_id::create("tx");

     forever
       begin
	  m_apb_if.monitor(tx_ok, tx.addr, tx.data, tx.write_mode);
	  if (tx_ok == '1)
	    begin
	       $cast(tx_clone, tx.clone());
	       analysis_port.write(tx_clone);
	    end
       end
      
    endtask
   
endclass

///////////////////////////////////////////////////////////
//
// Class: apb_analyzer
//
///////////////////////////////////////////////////////////

class apb_analyzer extends uvm_subscriber #(apb_transaction);
   `uvm_component_utils(apb_analyzer)

   int m_writes_to_dut = 0;
   int m_reads_from_dut = 0;   
   int m_writes_to_other = 0;
   int m_reads_from_other = 0;   
   int m_data_valids = 0;
   int m_data_conflicts = 0;   
   
   logic [31:0] m_register_data[];
   logic m_write_hits[];
   logic m_read_hits[];      
   
   apb_transaction tx;
   
   covergroup dut_write_coverage;
      write_cov: coverpoint tx.addr[6:2] iff (tx.write_mode == '1);
   endgroup 

   covergroup dut_read_coverage;
      read_cov: coverpoint tx.addr[6:2] iff (tx.write_mode == '0);
   endgroup 

   function new(string name, uvm_component parent);
      super.new(name, parent);
      dut_write_coverage = new();
      dut_read_coverage = new();      
   endfunction

   function void write(apb_transaction t);
      tx = t;
      dut_write_coverage.sample();
      dut_read_coverage.sample();      
      
      if (t.addr >= DUT_START_ADDRESS && t.addr <= DUT_END_ADDRESS)
	begin
	   if (t.write_mode == '1)
	     begin
		++m_writes_to_dut;
		m_register_data[(t.addr - DUT_START_ADDRESS)/4] = t.data;
		m_write_hits[(t.addr - DUT_START_ADDRESS)/4] = '1;
	     end
	   else
	     begin
		++m_reads_from_dut;
		m_read_hits[(t.addr - DUT_START_ADDRESS)/4] = '1;

		if (m_write_hits[(t.addr - DUT_START_ADDRESS)/4] == '0)
		  uvm_report_error("apb_analyzer", $sformatf("Read from uninitialized location %d of\n%p\n", (t.addr - DUT_START_ADDRESS)/4, m_register_data));
		
		assert(m_register_data[(t.addr - DUT_START_ADDRESS)/4] == t.data)
		  ++m_data_valids;
                else
		  begin
		         uvm_report_error("apb_analyzer", $sformatf("Invalid data read from %h (register %d), got %h, expected %h\n",
								    t.addr,
								    (t.addr - DUT_START_ADDRESS)/4,
								    t.data, m_register_data[(t.addr - DUT_START_ADDRESS)/4]));
		     ++m_data_conflicts;
		  end
	     end
	end
      else 
	begin
	   if (t.write_mode == '1)
	     ++m_writes_to_other;
	   else
	     ++m_reads_from_other;	     
	end

   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_register_data = new[(DUT_END_ADDRESS-DUT_START_ADDRESS+1)];
      m_write_hits = new[(DUT_END_ADDRESS-DUT_START_ADDRESS+1)];      
      for (int i=0; i < (DUT_END_ADDRESS-DUT_START_ADDRESS+1)/4; ++i)
	m_write_hits[i] = '0;
      m_read_hits = new[(DUT_END_ADDRESS-DUT_START_ADDRESS+1)];      
      for (int i=0; i < (DUT_END_ADDRESS-DUT_START_ADDRESS+1)/4; ++i)
	m_read_hits[i] = '0;
   endfunction

   function void report_phase( uvm_phase phase );
      int write_hits = 0;
      int read_hits = 0;      
      real write_coverage =  dut_write_coverage.get_coverage();
      real read_coverage =  dut_read_coverage.get_coverage();      
      for (int i=0; i < (DUT_END_ADDRESS-DUT_START_ADDRESS+1)/4; ++i)
	if (m_write_hits[i] == '1) ++write_hits;
      for (int i=0; i < (DUT_END_ADDRESS-DUT_START_ADDRESS+1)/4; ++i)
	if (m_read_hits[i] == '1) ++read_hits;
      uvm_report_info("apb_analyzer", $sformatf("DUT: Inidividual addresses accessed:  %6d writes, %6d reads", write_hits, read_hits));
      uvm_report_info("apb_analyzer", $sformatf("     Total accesses:                  %6d writes, %6d reads", m_writes_to_dut, m_reads_from_dut));
      uvm_report_info("apb_analyzer", $sformatf("     Coverage:                        %.2f%% write, %.2f%% read ", write_coverage, read_coverage));    
      uvm_report_info("apb_analyzer", $sformatf("     Read data:                       %6d valid,  %6d invalid", m_data_valids, m_data_conflicts));    
      uvm_report_info("apb_analyzer", $sformatf("Accesses to other APB addresses     : %6d writes, %6d reads", m_writes_to_other, m_reads_from_other));  
   endfunction
   

endclass


///////////////////////////////////////////////////////////
//
// Class: apb_sequencer
//
///////////////////////////////////////////////////////////

typedef uvm_sequencer #(apb_transaction) apb_sequencer;


///////////////////////////////////////////////////////////
//
// Class: apb_sequence_config
//
///////////////////////////////////////////////////////////

class apb_sequence_config extends uvm_object;
   int apb_test_cycles;
endclass 


///////////////////////////////////////////////////////////
//
// Class: apb_sequence
//
///////////////////////////////////////////////////////////

class apb_sequence extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(apb_sequence)

   function new (string name = "");
      super.new(name);
   endfunction

   task body;
      apb_sequence_config seq_config;
      int test_cycles = 100;
      int queue_index;
      apb_transaction write_queue[$];
      
      if (uvm_config_db #(apb_sequence_config)::get(null, get_full_name(), "apb_sequence_config", seq_config))
	begin
	   test_cycles = seq_config.apb_test_cycles;
	   `uvm_info("",$sformatf("apb_sequence configured to run for %d test cycles", test_cycles), UVM_NONE);	   
	end
   
      repeat(test_cycles)
	begin
	   apb_transaction write_tx;
	   apb_transaction read_tx;	      
	   int unsigned random_value;
	   
	   random_value = $urandom_range(1,3);	      
	   for (int i=0; i < random_value; ++i)
	     begin
		write_tx = apb_transaction::type_id::create("write_tx");
		assert( write_tx.randomize() );
		write_tx.addr &= 32'hFFFFFFFC;
		write_tx.write_mode = '1;	      
		write_tx.fail = 0;
		write_queue.push_back(write_tx);
		start_item(write_tx);
		finish_item(write_tx);
	     end

	   random_value = $urandom_range(1,3);	      
	   for (int i=0; i < random_value; ++i)
	     begin
		read_tx = apb_transaction::type_id::create("read_tx");	      	      
		assert( read_tx.randomize() );	      
		queue_index = $urandom_range( 0, (write_queue.size()-1) );
		read_tx.addr = write_queue[queue_index].addr;
		read_tx.write_mode = '0;
		read_tx.fail = '0;	      
		start_item(read_tx);
		finish_item(read_tx);
	     end
	end
   endtask

endclass 


///////////////////////////////////////////////////////////
//
// Class: apb_agent
//
///////////////////////////////////////////////////////////

class apb_agent extends uvm_agent;
   `uvm_component_utils(apb_agent)

   apb_driver m_driver;
   apb_monitor m_monitor;
   apb_analyzer m_analyzer;
   apb_sequencer m_sequencer;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_sequencer = apb_sequencer::type_id::create("m_sequencer", this);
      m_driver    = apb_driver::type_id::create("m_driver", this);
      m_monitor   = apb_monitor::type_id::create("m_monitor", this);
      m_analyzer   = apb_analyzer::type_id::create("m_analyzer", this);            
   endfunction

   function void connect_phase(uvm_phase phase);
      m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
      m_monitor.analysis_port.connect(m_analyzer.analysis_export);
   endfunction
   
endclass 

///////////////////////////////////////////////////////////
//
// Class: apb_env
//
///////////////////////////////////////////////////////////

class apb_env extends uvm_env;
   `uvm_component_utils(apb_env)

   apb_agent m_agent;
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_agent = apb_agent::type_id::create("m_agent", this);
   endfunction

endclass   


///////////////////////////////////////////////////////////
//
// Class: apb_test
//
///////////////////////////////////////////////////////////
   
class apb_test extends uvm_test;
  `uvm_component_utils(apb_test)
    
  function new(string name, uvm_component parent);
     super.new(name,parent);
  endfunction

   apb_env m_env;

   function void build_phase(uvm_phase phase);

      apb_sequence_config seq_config = new;
      int test_cycles;
      int apb_start_address;
      int apb_end_address;
      
      super.build_phase(phase);

      if (uvm_config_db #(int)::get(null, get_full_name(), "APB_TEST_CYCLES", test_cycles))
	seq_config.apb_test_cycles = test_cycles;
      else
	seq_config.apb_test_cycles = 100;

      
      uvm_config_db #(apb_sequence_config)::set(this, "*", "apb_sequence_config", seq_config);

      m_env = apb_env::type_id::create("m_env", this);
 
  endfunction: build_phase

   task run_phase(uvm_phase phase);
      apb_sequence seq;
      seq = apb_sequence::type_id::create("seq");
      phase.raise_objection(this); 
      seq.start( m_env.m_agent.m_sequencer );
      phase.drop_objection(this); 
    endtask

endclass 

`endif //  `ifndef SYNTHESIS
   
endpackage

   


