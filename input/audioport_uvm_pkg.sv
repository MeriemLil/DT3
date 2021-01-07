`include "audioport.svh"


package audioport_uvm_pkg;

// `define DEBUG 1


/////////////////////////////////////////////////////////
//
//    audioport_predictor
//    audioport_comparator
//    audioport_scoreboard
//    audioport_env
//    audioport_sequence_config
//    audioport_main_sequence
//    audioport_isr_sequence
//    audioport_master_sequence      
//    audioport_uvm_test
//
/////////////////////////////////////////////////////////

`include "uvm_macros.svh"
   import uvm_pkg::*;
   import audioport_pkg::*;
   import audioport_util_pkg::*;   
   import apb_uvm_pkg::*;
   import control_unit_uvm_pkg::*;   
   import irq_agent_uvm_pkg::*;   
   import i2s_agent_uvm_pkg::*;
   
///////////////////////////////////////////////////////////
//
// audioport_predictor
//
// This component implements a reference mode for the
// audioport. It receives APB transactions from the apb_monitor
// through an analysis export,  and transmits responses to the 
// audioport_comparator through a get export.
//
///////////////////////////////////////////////////////////

class audioport_predictor extends uvm_component;
   `uvm_component_utils(audioport_predictor)
   
   uvm_analysis_imp #(apb_transaction, audioport_predictor) apb_analysis_export;
   uvm_nonblocking_get_imp #(i2s_transaction, audioport_predictor) predictor_get_export;

   // ----------------------------------------------------------------------------------
   // Registers
   // ----------------------------------------------------------------------------------

   logic [31:0] 		    cmd_r = '0;
   logic [31:0] 		    level_r = '0;      
   logic [31:0] 		    cfg_r = '0;
   logic [DSP_REGISTERS-1:0][31:0] 	    dsp_regs_r = '0;   
   logic [ABUF_REGISTERS-1:0][23:0] abuf_r;
   int 				    abuf_read_counter_r = 0;
   logic 			    play_mode = '0;
   
   // ----------------------------------------------------------------------------------
   // filter coefficients
   // ----------------------------------------------------------------------------------
   
   logic signed [DSP_REGISTERS-1:0][31:0] active_dsp_regs = '0;

   // ----------------------------------------------------------------------------------
   // scaler levels
   // ----------------------------------------------------------------------------------
   
   logic [1:0][15:0] active_level_data = '0;

   // ----------------------------------------------------------------------------------
   // config register(s) loaded with CONFIG command
   // ----------------------------------------------------------------------------------
   
   logic [31:0] active_config_data = '0;            

   // ----------------------------------------------------------------------------------
   // dsp_unit filter and output registers
   // ----------------------------------------------------------------------------------

   logic signed [1:0][23:0] dsp_inputs;         
   logic signed [1:0][23:0] filter_outputs;
   logic signed [1:0][23:0] dsp_outputs;      
   
   logic signed [FILTER_TAPS-1:0][1:0][23:0] filter_data = '0;
   logic [1:0][23:0] 		  audio_outputs = '0;

   // ----------------------------------------------------------------------------------
   // Predictor output queue
   // ----------------------------------------------------------------------------------
   
   i2s_transaction output_queue[$];
   int delete_queue_on_start = 0;
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      apb_analysis_export = new("apb_analysis_export", this);      
      predictor_get_export = new("predictor_get_port", this);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      play_mode = '0;
    endfunction

   // ----------------------------------------------------------------------------------
   // write method for the analysis export.
   // ----------------------------------------------------------------------------------
   
   function void write(apb_transaction t);
      apb_transaction tx = t;
      
      if (t.write_mode == '1)
	begin
	   if (tx.addr == CMD_REG_APB_ADDRESS)
	     begin
`ifdef DEBUG
		$display("%f: audioport_predictor: CMD_REG = %h", $realtime, tx.data);
`endif
		cmd_r = tx.data;
		case (cmd_r[31:24])
		  CMD_START:
		    begin
		       play_mode = '1;
		       if (delete_queue_on_start) output_queue.delete();
		       delete_queue_on_start = 0;
		       repeat(FIFO_SIZE+1) 
			 do_dsp();
		       
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_START -------------------------------------------------------------------------------", $realtime);
`endif
		    end
		  CMD_STOP:
		    begin
		       play_mode = '0;	
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_STOP -------------------------------.------------------------------------------------", $realtime);
`endif
		    end
		  CMD_CFG:
		    begin
		       do_configs();	
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_CFG -------------------------------.------------------------------------------------", $realtime);
`endif
		    end
		  CMD_LEVEL:
		    begin
		    set_levels(level_r);
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_LEVEL -------------------------------.------------------------------------------------", $realtime);
`endif
		    end
		  CMD_CLR:
		    begin
		       do_clear();
		       delete_queue_on_start = 1;		       
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_CLR ---------------------------------------------------------------------------------", $realtime);
`endif
		    end
		endcase
		
	     end
	   else if (tx.addr == LEVEL_REG_APB_ADDRESS)
	     begin
		level_r = tx.data;
`ifdef DEBUG
		$display("%f: audioport_predictor: LEVEL_REG = %h", $realtime, tx.data);		
`endif
	     end
	   else if (tx.addr == CFG_REG_APB_ADDRESS)
	     begin
		cfg_r = tx.data;
`ifdef DEBUG
		$display("%f: audioport_predictor: CFG_REG = %h", $realtime, tx.data);		
`endif
	     end
	   else if (tx.addr >= DSP_REGS_START_APB_ADDRESS && tx.addr <= DSP_REGS_END_APB_ADDRESS)
	     begin
		int int_addr = (tx.addr - DSP_REGS_START_APB_ADDRESS)/4;
		dsp_regs_r[int_addr] = tx.data;
`ifdef DEBUG
		$display("%f: audioport_predictor: dsp_regs_r[%d] = %h", $realtime, int_addr, dsp_regs_r[int_addr]);				
`endif
	     end
	   else if (tx.addr >= ABUF0_START_APB_ADDRESS && tx.addr <= ABUF1_END_APB_ADDRESS)
	     begin
		int int_addr = (tx.addr - ABUF0_START_APB_ADDRESS)/4;		
		abuf_r[int_addr] = tx.data[23:0];
`ifdef DEBUG
		$display("%f: audioport_predictor: abuf_r[%d] = %d", $realtime, int_addr, $signed(abuf_r[int_addr]));						
`endif
	     end
	   else
	     begin
`ifdef DEBUG
		$display("%f: audioport_predictor: Out-of-band address %h", $realtime, tx.addr);						
`endif
	     end
	end
   endfunction

   // ----------------------------------------------------------------------------------
   // can_get method tells if data are available
   // ----------------------------------------------------------------------------------
   
   function bit can_get();
      return 1;
   endfunction

   // ----------------------------------------------------------------------------------
   // try_get method that allows audioport_comparator to get next reference value
   // ----------------------------------------------------------------------------------
   
   function int try_get(output i2s_transaction t);
      t = output_queue.pop_front();
      do_dsp();
      
`ifdef DEBUG
      $display("%f: audioport_predictor: queue_size = %d", $realtime, output_queue.size());
`endif
`ifdef DEBUG
      $display("%f: audioport_predictor: audio out = %d, %d", $realtime, $signed(t.audio_data[0]), $signed(t.audio_data[1]));
`endif
      
      return 1;
   endfunction
 

   // ----------------------------------------------------------------------------------
   // Method for executing CMD_CFG: copy from input variables to 'active' variables
   // ----------------------------------------------------------------------------------
   
   function void do_configs();
      active_config_data = cfg_r;
      for (int i=0; i < DSP_REGISTERS; ++i)
	begin
	   active_dsp_regs[i] = dsp_regs_r[i];
	end
   endfunction

   // ----------------------------------------------------------------------------------
   // Method for executing CMD_CLR: reset variables
   // ----------------------------------------------------------------------------------

   function void do_clear();
      for(int j=0; j < ABUF_REGISTERS; ++j)
	begin
	   abuf_r[j] = '0;
	end
      
      for(int j=0; j < FILTER_TAPS; ++j)
	begin
	   filter_data[j][0] = '0;
	   filter_data[j][1] = '0;		
	end
      abuf_read_counter_r = 0;
      dsp_inputs[0] = '0;
      dsp_inputs[1] = '0;
      dsp_outputs[0] = '0;
      dsp_outputs[1] = '0;
      audio_outputs[0] = '0;
      audio_outputs[1] = '0;
   endfunction

   // ----------------------------------------------------------------------------------
   // do_dsp: Helper method for executing 'dsp_unit'
   // ----------------------------------------------------------------------------------

   function void do_dsp();

      logic signed [23:0] d;
      logic signed [31:0] c;      
      logic signed [32+24+FILTER_TAPS-1:0] accu30L, accu330L, accu30R, accu330R;
      logic signed [32+24+FILTER_TAPS:0] sumL, sumR;	   
      logic signed [16:0] 		levelL = active_level_data[0];
      logic signed [16:0] 		levelR = active_level_data[1];		
      logic signed [41:0] 		scaledL;
      logic signed [41:0] 		scaledR;
      i2s_transaction i2s_tx = new();      

`ifdef DEBUG
      $display("%f: audioport_predictor: abuf read counter = %d", $realtime, abuf_read_counter_r);
`endif
      dsp_inputs[0] = abuf_r[abuf_read_counter_r];
      abuf_read_counter_r = abuf_read_counter_r + 1;
      dsp_inputs[1] = abuf_r[abuf_read_counter_r];
      abuf_read_counter_r = abuf_read_counter_r + 1;
      if (abuf_read_counter_r >= 4*AUDIO_BUFFER_SIZE-1)
	abuf_read_counter_r = 0;
      
      // Filter
`ifdef DEBUG
      $display("%f: audioport_predictor: abuf_out = %d %d", $realtime, $signed(dsp_inputs[0]), $signed(dsp_inputs[1]));	   
`endif      
      if (active_config_data[CFG_FILTER] == '1)
	begin
	   for (int tap=FILTER_TAPS-1; tap > 0; --tap)
	     begin
		filter_data[tap][0] = filter_data[tap-1][0];
		filter_data[tap][1] = filter_data[tap-1][1];			  
	     end
	   filter_data[0][0] = dsp_inputs[0];
	   filter_data[0][1] = dsp_inputs[1];
	   
	   accu30L = 0;
	   accu330L = 0;
	   accu30R = 0;
	   accu330R = 0;

	   for (int tap=0; tap < FILTER_TAPS; ++tap)
	     begin
		logic signed [32+24-1:0] mul;
		d = filter_data[tap][0];
		c = active_dsp_regs[tap];
		mul = c * d;
		accu30L = accu30L + mul;
		d = filter_data[tap][1];
		c = active_dsp_regs[FILTER_TAPS+tap];
		mul = c * d;
		accu30R = accu30R + mul;
		d = filter_data[tap][0];
		c = active_dsp_regs[2*FILTER_TAPS+tap];
		mul = c * d;
		accu330L = accu330L + mul;
		d = filter_data[tap][1];
		c = active_dsp_regs[3*FILTER_TAPS+tap];
		mul = c * d;
		accu330R = accu330R + mul;
	     end 
	   
	   sumL = accu30L + accu330R;
	   sumR = accu30R + accu330L;
	   sumL = (sumL >>> 31);
	   sumR = (sumR >>> 31);	   
	   filter_outputs[0] = sumL;
	   filter_outputs[1] = sumR;
	end
      else
	begin
	   filter_outputs[0] = dsp_inputs[0];
	   filter_outputs[1] = dsp_inputs[1];
	end
`ifdef DEBUG
      $display("%f: audioport_predictor: scaler in = %d %d", $realtime, $signed(filter_outputs[0]), $signed(filter_outputs[1]));
`endif      
      // scaler
      
      scaledL = signed'(filter_outputs[0]);
      scaledR = signed'(filter_outputs[1]);
      levelL = '0;
      levelR = '0;
      levelL[15:0] = active_level_data[0];
      levelR[15:0] = active_level_data[1];
      
      scaledL = scaledL * levelL;
      scaledR = scaledR * levelR;		
      scaledL = scaledL >>> 15;
      scaledR = scaledR >>> 15;		
      
      if (active_config_data[CFG_MONO] == '0)
	begin
	   dsp_outputs[0] = scaledL;
	   dsp_outputs[1] = scaledR;
	end
      else
	begin
	   scaledR = scaledR >>> 1;
	   scaledL = scaledL >>> 1;	   
	   dsp_outputs[0] = (scaledL + scaledR);
	   dsp_outputs[1] = dsp_outputs[0];
	end
`ifdef DEBUG
      $display("%f: audioport_predictor dsp_unit out = %d %d", $realtime, $signed(dsp_outputs[0]), $signed(dsp_outputs[1]));      
`endif
      audio_outputs[0] = dsp_outputs[0];
      audio_outputs[1] = dsp_outputs[1];	         

      i2s_tx.audio_data[0] = audio_outputs[0];
      i2s_tx.audio_data[1] = audio_outputs[1];	   
      output_queue.push_back(i2s_tx);
      
endfunction

   // ----------------------------------------------------------------------------------
   // set_levels: Method for setting levels from level register
   // ----------------------------------------------------------------------------------
   
   function void set_levels(logic [31:0] level_setting);
      active_level_data[0] = level_setting[15:0];
      active_level_data[1] = level_setting[31:16];		
   endfunction


   task run_phase(uvm_phase phase);
      time delay;
      forever
	begin
	   wait (play_mode);
	   while(play_mode)
	     begin
		case (active_config_data[1:0])
		  RATE_48000:
		    delay = 0.02083333ms;
//		    delay = CLK_DIV_48000*CLK_PERIOD;
		  RATE_96000:
		    delay = 0.01041666ms;
//		    delay = CLK_DIV_96000*CLK_PERIOD;
		  RATE_192000:
		    delay = 0.00520833ms;
//		    delay = CLK_DIV_192000*CLK_PERIOD;		  
		endcase 
//		do_dsp();
`ifdef DEBUG		
		$info("%d", abuf_read_counter_r);
`endif
		#(delay);


	     end
	end
    endtask

endclass

///////////////////////////////////////////////////////////
//
// audioport_comparator
//
// This component receives I2S transactions from the i2s_agent
// through its analysis export, then gets reference data values
// from the audioport_predictor through its get port, and
// writes both results to a text file.
//
///////////////////////////////////////////////////////////
   
class audioport_comparator extends uvm_component;
   `uvm_component_utils(audioport_comparator)
     
   uvm_analysis_imp #(i2s_transaction, audioport_comparator) i2s_analysis_export;
   uvm_nonblocking_get_port #(i2s_transaction) predictor_get_port;
   int file;
   int m_samples = 0;
   int m_errors = 0;
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      i2s_analysis_export = new("i2s_analysis_export", this);      
      predictor_get_port = new("predictor_get_port", this);
   endfunction 

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      file = $fopen("results/audioport_uvm_comparator_out.txt", "w");
   endfunction
   
   function void write(i2s_transaction t);
      i2s_transaction dut_tx = t;
      i2s_transaction ref_tx;      
      int tmp;
      
      tmp = predictor_get_port.try_get(ref_tx);

      if (ref_tx != null)
	begin 
	   ++m_samples;
	   
	   assert((dut_tx.audio_data[0] == ref_tx.audio_data[0]) &&
		  (dut_tx.audio_data[1] == ref_tx.audio_data[1]))	     
	     else
	       begin
		  $error("%10f: audioport_comparator: DUT=%11d%11d  REF=%11d%11d", 
			 $realtime/1000000000.0, 
			 signed'(dut_tx.audio_data[0]), signed'(dut_tx.audio_data[1]), 
			 signed'(ref_tx.audio_data[0]), signed'(ref_tx.audio_data[1]));
		  ++m_errors;
	       end
`ifdef DEBUG
	   $display("%10f: audioport_comparator: DUT=%11d%11d  REF=%11d%11d", 
		    $realtime/1000000000.0, 
		    signed'(dut_tx.audio_data[0]), signed'(dut_tx.audio_data[1]), 
		    signed'(ref_tx.audio_data[0]), signed'(ref_tx.audio_data[1]));
`endif
	   $fwrite(file, "%10f", $realtime/1000000000.0);
	   $fwrite(file, "%11d%11d", signed'(dut_tx.audio_data[0]), signed'(dut_tx.audio_data[1]));
	   $fwrite(file, "%11d%11d", signed'(ref_tx.audio_data[0]), signed'(ref_tx.audio_data[1]));
	   $fwrite(file, "\n");
	end // if (ref_tx != null)
      else
	begin
`ifdef DEBUG
	   $display("ref_ex == null in audioport_comparator");
`endif
	end
   endfunction

   function void report_phase( uvm_phase phase );
      uvm_report_info("audioport_comparator", $sformatf("%d samples compared, %d differences detected", m_samples, m_errors));
   endfunction
   
   
endclass

///////////////////////////////////////////////////////////
//
// audioport_scoreboard
//
// This component instantiates the audioprot_comparator and 
// audioport_predictor and connects them
//
///////////////////////////////////////////////////////////
   
class audioport_scoreboard extends uvm_scoreboard;
   `uvm_component_utils(audioport_scoreboard)

   audioport_predictor m_predictor;
   audioport_comparator m_comparator;   
   uvm_analysis_export #(apb_transaction) apb_analysis_export;
   uvm_analysis_export #(i2s_transaction) i2s_analysis_export;   

   function new(string name, uvm_component parent);
      super.new(name, parent);
      apb_analysis_export = new("apb_analysis_export", this);
      i2s_analysis_export = new("i2s_analysis_export", this);      
   endfunction 
   
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_predictor = audioport_predictor::type_id::create("m_predictor", this);
      m_comparator = audioport_comparator::type_id::create("m_comparator", this);                  
   endfunction
     
   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      apb_analysis_export.connect(m_predictor.apb_analysis_export);
      i2s_analysis_export.connect(m_comparator.i2s_analysis_export);
      m_comparator.predictor_get_port.connect(m_predictor.predictor_get_export);
   endfunction
     
endclass

   
///////////////////////////////////////////////////////////
//
// audioport_env
//
///////////////////////////////////////////////////////////

class audioport_env extends uvm_env;
   `uvm_component_utils(audioport_env)

   // ----To do UVM1: Declare member variables to hold components -----------

   // ------------------------------------------------------------------------

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // ----To do UVM2: Create components --------------------------------------

      // ------------------------------------------------------------------------
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // ----To do UVM3: Create port-to-export connections ----------------------

      // ------------------------------------------------------------------------
   endfunction
   
endclass   


///////////////////////////////////////////////////////////
//
// Class: audioport_sequence_config
//
///////////////////////////////////////////////////////////

class audioport_sequence_config extends uvm_object;
   int current_abuf = 0;
   int phase_accu = 0;
   int ramp_counter = 0;

   // ----------------------------------------------------------------------------------
   // signal_generator: Square wave generator
   // ----------------------------------------------------------------------------------

   function logic [23:0] square_generator();
      int mod = 32;
      logic signed [23:0] sig;
      logic signed [16:0] noise;
      
      if (phase_accu % mod <= mod/2)
	sig = 24'h100000;
      else
	sig = 24'he00000;
      ++phase_accu;
      return unsigned'(sig);
   endfunction

   // ----------------------------------------------------------------------------------
   // signal_generator: Ramp wave generator
   // ----------------------------------------------------------------------------------

   function logic [23:0] ramp_generator();
      const int step = 24'h100000/16;
      logic signed [23:0] sig;
      logic signed [16:0] noise;

      ramp_counter = ramp_counter + step;
      sig = ramp_counter;
      if (ramp_counter >= signed'(24'h100000))
	ramp_counter = signed'(24'he00000);	

      return unsigned'(sig);
   endfunction

   function void reset();
      current_abuf = 0;
      phase_accu = 0;
      ramp_counter = 0;
   endfunction
   
endclass 
   
///////////////////////////////////////////////////////////
//
// audioport_main_sequence
//
///////////////////////////////////////////////////////////
   

class audioport_main_sequence extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(audioport_main_sequence)

   function new (string name = "");
      super.new(name);
   endfunction
   
   // ----------------------------------------------------------------------------------
   // sequence body task
   // ----------------------------------------------------------------------------------
      
   task body;
      apb_transaction write_tx;
      audioport_sequence_config seq_config;
      
      logic signed [31:0] input_data;
      logic [31:0] 	  level_data = 32'h80008000;
      logic [15:0] 	  level_value;
      logic [31:0] 	  cfg_data = 32'hfffffff0;
      int 		  current_abuf = 0;
      logic [4*FILTER_TAPS-1:0][31:0] filter_taps;
      uvm_event irq_event;
      irq_event = uvm_event_pool::get_global("irq_out");
      
      if (read_filter_taps(filter_taps) == 0)
	begin
	   $info("Using default filter coefficients.");
	end

      if (uvm_config_db #(audioport_sequence_config)::get(null, get_full_name(), "audioport_sequence_config", seq_config))
	begin
	   seq_config.current_abuf = 0;
	   uvm_config_db #(audioport_sequence_config)::set(null, "*", "audioport_sequence_config", seq_config);
	end
      else
	uvm_report_error("audioport_main_sequence.body:", "Could not get config data from uvm_config_db");
      
      write_tx = apb_transaction::type_id::create("write_tx");

      $info("Progam filter");
      
      for(int unsigned i=0; i < DSP_REGISTERS; ++i)
	begin
	   write_tx.addr = DSP_REGS_START_APB_ADDRESS +4*i;
	   write_tx.data = filter_taps[i];
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	end


      $info("Fill ABUF");

      
      for(int unsigned i=0; i < 4*AUDIO_BUFFER_SIZE; i = i+2)
	begin
	   logic signed [23:0] audioL = seq_config.square_generator();
	   logic signed [23:0] audioR = seq_config.ramp_generator();	   	   
	   write_tx.addr = ABUF0_START_APB_ADDRESS + 4*i;
	   write_tx.data =  audioL;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	   write_tx.addr = ABUF0_START_APB_ADDRESS + 4*(i+1);
	   write_tx.data = audioR;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	end

      
      #2us;
      $info("Set level");
      
      write_tx.addr = LEVEL_REG_APB_ADDRESS;
      write_tx.data = {32'h80008000};
      write_tx.write_mode = '1;	      
      write_tx.fail = 0;
      start_item(write_tx);
      finish_item(write_tx);
      
      write_tx.addr = CMD_REG_APB_ADDRESS;
      write_tx.data = { CMD_LEVEL, 24'h000000 };
      write_tx.write_mode = '1;	      
      write_tx.fail = 0;
      start_item(write_tx);
      finish_item(write_tx);
      
      #2us;      

      for(int test_counter = 1; test_counter <= 5; ++test_counter)
	begin
	   
	   case (test_counter)
	     1:
	       begin
		  $info("%2.2fus Test %0d: 192kHz", $realtime/1000.0, test_counter);
		  write_tx.addr = CFG_REG_APB_ADDRESS;
		  write_tx.data = { 30'b00000000_00000000_00000000_000010, RATE_192000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  write_tx.addr = CMD_REG_APB_ADDRESS;
		  write_tx.data = { CMD_CFG, 24'h000000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
	       end
	     2:
	       begin
		  $info("%2.2fus Test %0d: 96kHz", $realtime/1000.0, test_counter);		  
		  write_tx.addr = CFG_REG_APB_ADDRESS;
		  write_tx.data = { 30'b00000000_00000000_00000000_000010, RATE_96000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  write_tx.addr = CMD_REG_APB_ADDRESS;
		  write_tx.data = { CMD_CFG, 24'h000000 };		  
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  		  
	       end 
	     3:
	       begin
		  $info("%2.2fus Test %0d: 48kHz", $realtime/1000.0, test_counter);		  		  
		  write_tx.addr = CFG_REG_APB_ADDRESS;
		  write_tx.data = { 30'b00000000_00000000_00000000_000010, RATE_48000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  write_tx.addr = CMD_REG_APB_ADDRESS;
		  write_tx.data = { CMD_CFG, 24'h000000 };		  
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  		  
	       end

	     4:
	       begin
		  $info("%2.2fus Test %0d: 192kHz, level scaling", $realtime/1000.0, test_counter);		  		  		  
		  write_tx.addr = CFG_REG_APB_ADDRESS;
		  write_tx.data = { 30'b00000000_00000000_00000000_000011, RATE_192000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  write_tx.addr = CMD_REG_APB_ADDRESS;
		  write_tx.data = { CMD_CFG, 24'h000000 };		  
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  // Initial level value is 1.0
		  level_value = 16'h8000;
	       end

	     5:
	       begin
		  $info("%2.2fus Test %0d: 192kHz, filter OFF", $realtime/1000.0, test_counter);		  		  		  		  
		  write_tx.addr = CFG_REG_APB_ADDRESS;
		  write_tx.data = { 30'b00000000_00000000_00000000_000000, RATE_192000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  write_tx.addr = CMD_REG_APB_ADDRESS;
		  write_tx.data = { CMD_CFG, 24'h000000 };		  
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);

		  // Restore max level
		  write_tx.addr = LEVEL_REG_APB_ADDRESS;
		  write_tx.data = {32'h80008000};
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);

		  write_tx.addr = CMD_REG_APB_ADDRESS;
		  write_tx.data = { CMD_LEVEL, 24'h000000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
	       end
	     
	   endcase
	   

	   #2us;	   
	   $info("Start");
	   write_tx.addr = CMD_REG_APB_ADDRESS;
	   write_tx.data = { CMD_START, 24'h000000 }; 
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);


	   if (test_counter != 4)
	     begin
		#2ms;
	     end
	   else
	     begin
		for (int level = 0; level < 128; ++level)
		  begin
		     #0.015625ms; // 2ms/128
		     level_value -= (16'h8000/127);
		     level_data = { level_value, level_value };
		     
		     write_tx.addr = LEVEL_REG_APB_ADDRESS;
		     write_tx.data = level_data;
		     write_tx.write_mode = '1;	      
		     write_tx.fail = 0;
		     start_item(write_tx);
		     finish_item(write_tx);
		     
		     write_tx.addr = CMD_REG_APB_ADDRESS;
		     write_tx.data = { CMD_LEVEL, 24'h000000 };
		     write_tx.write_mode = '1;	      
		     write_tx.fail = 0;
		     start_item(write_tx);
		     finish_item(write_tx);
		  end
	     end 


	   #5us;	   
	   $info("Stop");
	   write_tx.addr = CMD_REG_APB_ADDRESS;
	   write_tx.data = { CMD_STOP, 24'h000000 }; 
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);

	   #30us;	 
	   $info("Clear");  

	   seq_config.reset();
	   current_abuf = 0;

	   write_tx.addr = CMD_REG_APB_ADDRESS;
	   write_tx.data = { CMD_CLR, 24'h000000}; 
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	   
	   #10us;

	   $info("Fill ABUF");  
	   for(int unsigned i=0; i < 4*AUDIO_BUFFER_SIZE; i = i+2)
	     begin
		logic signed [23:0] audioL = seq_config.square_generator();
		logic signed [23:0] audioR = seq_config.ramp_generator();	   	   
		write_tx.addr = ABUF0_START_APB_ADDRESS + 4*i;
		write_tx.data =  audioL;
		write_tx.write_mode = '1;	      
		write_tx.fail = 0;
		start_item(write_tx);
		finish_item(write_tx);
		write_tx.addr = ABUF0_START_APB_ADDRESS + 4*(i+1);
		write_tx.data = audioR;
		write_tx.write_mode = '1;	      
		write_tx.fail = 0;
		start_item(write_tx);
		finish_item(write_tx);
	     end

	   if (uvm_config_db #(audioport_sequence_config)::get(null, get_full_name(), "audioport_sequence_config", seq_config))
	     begin
		seq_config.current_abuf = 0;
		uvm_config_db #(audioport_sequence_config)::set(null, "*", "audioport_sequence_config", seq_config);
	     end
	   else
	     uvm_report_error("audioport_main_sequence.body:", "Could not get config data from uvm_config_db");
	   
	end 
      
      
      // ----To do: Add your own tests here ------------------------------------

      // ------------------------------------------------------------------------


   endtask

endclass 

///////////////////////////////////////////////////////////
//
// audioport_isr_sequence
//
///////////////////////////////////////////////////////////

class audioport_isr_sequence extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(audioport_isr_sequence)

   function new (string name = "");
      super.new(name);
   endfunction

   task body;
      apb_transaction write_tx;
      audioport_sequence_config seq_config;
      int current_abuf = 0;
      write_tx = apb_transaction::type_id::create("write_tx");

      // Take over sequencer
      m_sequencer.grab(this);

      // Get sequence config object to find out current buffer number
      if (uvm_config_db #(audioport_sequence_config)::get(null, get_full_name(), "audioport_sequence_config", seq_config))
	begin
	   current_abuf = seq_config.current_abuf;
	end
      else
	uvm_report_error("audioport_isr_sequence.body:", "Could not get config data from uvm_config_db");

      // Mimic interrupt latency
      #(INTERRUPT_LATENCY);

      // Fill next buffer
      for(int unsigned i=0; i < AUDIO_BUFFER_SIZE; ++i)
	begin
	   logic signed [23:0] audioL = seq_config.square_generator();
	   logic signed [23:0] audioR = seq_config.ramp_generator();	   	   
	   if (current_abuf == 0)
	     write_tx.addr = ABUF0_START_APB_ADDRESS + (i*2)*4;
	   else
	     write_tx.addr = ABUF1_START_APB_ADDRESS + (i*2)*4;			      
	   write_tx.data = audioL;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	   
	   if (current_abuf == 0)
	     write_tx.addr = ABUF0_START_APB_ADDRESS + (i*2+1)*4;
	   else
	     write_tx.addr = ABUF1_START_APB_ADDRESS + (i*2+1)*4;			      
	   write_tx.data = audioR;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	end

      // Update buffer number and write back to database
      if (current_abuf == 0)
	seq_config.current_abuf = 1;
      else
	seq_config.current_abuf = 0;
      uvm_config_db #(audioport_sequence_config)::set(null, "*", "audioport_sequence_config", seq_config);
      
      // Release sequencer
      m_sequencer.ungrab(this);
   endtask
endclass
   

///////////////////////////////////////////////////////////
//
// audioport_master_sequence
//
///////////////////////////////////////////////////////////

class audioport_master_sequence extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(audioport_master_sequence)

   function new (string name = "");
      super.new(name);
   endfunction

   task body;
      audioport_main_sequence main_seq;
      audioport_isr_sequence isr_seq;      
      uvm_event irq_event;
      audioport_sequence_config seq_config = new;
      
      main_seq = audioport_main_sequence::type_id::create("main_seq");
      isr_seq = audioport_isr_sequence::type_id::create("isr_seq");            
      irq_event = uvm_event_pool::get_global("irq_out");

      // Initialize sequence config data
      seq_config.current_abuf = 0;
      uvm_config_db #(audioport_sequence_config)::set(null, "*", "audioport_sequence_config", seq_config);
      
      fork
	 main_seq.start(m_sequencer); // Start main sequence
	 begin // In parallel: start interrut handling process loop
	    forever 
	      begin
		 irq_event.wait_trigger(); // Wait for interrupt event
		 isr_seq.start(m_sequencer); // Run interrupt service sequence once
	      end
	 end
      join_any
      disable fork; // If main sequence end, end everything

   endtask

endclass

///////////////////////////////////////////////////////////
//
// audioport_test
//
///////////////////////////////////////////////////////////
   
class audioport_uvm_test extends uvm_test;
  `uvm_component_utils(audioport_uvm_test)

   audioport_env m_env;
    
  function new(string name, uvm_component parent);
     super.new(name,parent);
  endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_env = audioport_env::type_id::create("m_env", this);
  endfunction: build_phase

   task run_phase(uvm_phase phase);
      // ----To do UVM4: Create master sequence and run it on control unit agent's
      //                 sequencer


      // ------------------------------------------------------------------------

    endtask

endclass 

endpackage
   

