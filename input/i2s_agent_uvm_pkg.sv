package i2s_agent_uvm_pkg;

`ifndef SYNTHESIS
   import audioport_pkg::*;
   
/////////////////////////////////////////////////////////
//
//    i2s_transaction
//    i2s_monitor
//    i2s_agent
//
/////////////////////////////////////////////////////////

`include "uvm_macros.svh"
import uvm_pkg::*;

///////////////////////////////////////////////////////////
//
// i2s_transaction
//
///////////////////////////////////////////////////////////

class i2s_transaction extends uvm_sequence_item;
   `uvm_object_utils(i2s_transaction)
  
     logic [1:0][23:0] audio_data;
   
   function new (string name = "");
      super.new(name);
   endfunction
   
   function void do_copy(uvm_object rhs);
      i2s_transaction rhs_;
      if(!$cast(rhs_, rhs)) begin
	 uvm_report_error("i2s_transaction.do_copy:", "Cast failed");
	 return;
      end
      super.do_copy(rhs); 
      audio_data[0] = rhs_.audio_data[0];
      audio_data[1] = rhs_.audio_data[1];	   
      
   endfunction

  function void do_record(uvm_recorder recorder);
   super.do_record(recorder);
   `uvm_record_attribute(recorder.tr_handle, "audio_data", audio_data);
   endfunction
   
endclass: i2s_transaction

///////////////////////////////////////////////////////////
//
// i2s_monitor
//
///////////////////////////////////////////////////////////

class i2s_monitor extends uvm_monitor;
   `uvm_component_utils(i2s_monitor)

   uvm_analysis_port #(i2s_transaction) analysis_port;
   
   virtual i2s_if m_i2s_if;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      analysis_port = new("analysis_port", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      if (!uvm_config_db #(virtual interface i2s_if)::get(this, "", "i2s_if_config", m_i2s_if))
	begin
	   `uvm_error("i2s_monitor config error" , "uvm_config_db #( virtual interface i2s_if )::get cannot find resource i2s_if" );
	end

   endfunction

   task run_phase(uvm_phase phase);
      logic tx_ok;
      
      i2s_transaction tx, tx_clone;      
      tx = i2s_transaction::type_id::create("tx");

     forever
       begin
	  m_i2s_if.monitor(tx_ok, tx.audio_data);
	  if (tx_ok == '1)
	    begin
	       $cast(tx_clone, tx.clone());
	       analysis_port.write(tx_clone);
	    end
	  else
	    begin
	       $display("i2s_monitor: transaction failed!\n");
	    end
       end
      
    endtask
   
endclass

///////////////////////////////////////////////////////////
//
// i2s_agent
//
///////////////////////////////////////////////////////////

class i2s_agent extends uvm_agent;
   `uvm_component_utils(i2s_agent)

   i2s_monitor m_monitor;
   uvm_analysis_port #(i2s_transaction) analysis_port;
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      analysis_port = new("analysis_port", this);
      
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_monitor   = i2s_monitor::type_id::create("m_monitor", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      m_monitor.analysis_port.connect(analysis_port);      
   endfunction
   
endclass 


   
`endif
   
endpackage




