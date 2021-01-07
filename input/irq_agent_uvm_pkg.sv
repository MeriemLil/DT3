package irq_agent_uvm_pkg;

`ifndef SYNTHESIS   

/////////////////////////////////////////////////////////
//
//    irq_transaction
//    irq_monitor
//    irq_agent
//
/////////////////////////////////////////////////////////

`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////////////////
//
// irq_transaction
//
///////////////////////////////////////////////////////////

class irq_transaction extends uvm_sequence_item;
   `uvm_object_utils(irq_transaction)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     
   logic irq;

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new (string name = "");
      super.new(name);
   endfunction
   
   function void do_copy(uvm_object rhs);
      irq_transaction rhs_;
      if(!$cast(rhs_, rhs)) begin
	 uvm_report_error("irq_transaction.do_copy:", "Cast failed");
	 return;
      end
      super.do_copy(rhs); 
      irq = rhs_.irq;
   endfunction

  function void do_record(uvm_recorder recorder);
   super.do_record(recorder);
   `uvm_record_attribute(recorder.tr_handle, "irq", irq);
   endfunction
   
endclass: irq_transaction



///////////////////////////////////////////////////////////
//
// irq_monitor
//
///////////////////////////////////////////////////////////

class irq_monitor extends uvm_monitor;
   `uvm_component_utils(irq_monitor)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     
   uvm_analysis_port #(irq_transaction) analysis_port;
   virtual irq_out_if m_irq_out_if;

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      analysis_port = new("analysis_port", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      if (!uvm_config_db #(virtual interface irq_out_if)::get(this, "", "irq_out_if_config", m_irq_out_if))
	begin
	   `uvm_error("irq_monitor config error" , "uvm_config_db #( virtual interface irq_out_if )::get cannot find resource irq_out_if" );
	end
   endfunction

   task run_phase(uvm_phase phase);
      irq_transaction tx, tx_clone;      
      tx = irq_transaction::type_id::create("tx");
     forever
       begin
	  m_irq_out_if.monitor(tx.irq);
	  $cast(tx_clone, tx.clone());
	  analysis_port.write(tx_clone);
       end
    endtask
   
endclass


///////////////////////////////////////////////////////////
//
// irq_agent
//
///////////////////////////////////////////////////////////

class irq_agent extends uvm_agent;
   `uvm_component_utils(irq_agent)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     
   uvm_analysis_port #(irq_transaction) analysis_port;
   irq_monitor m_monitor;

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      analysis_port = new("analysis_port", this);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_monitor   = irq_monitor::type_id::create("m_monitor", this);
   endfunction

   function void connect_phase(uvm_phase phase);
     m_monitor.analysis_port.connect(analysis_port);
   endfunction
   
endclass 

`endif

endpackage
   


