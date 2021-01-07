`include "audioport.svh"

///////////////////////////////////////////////////////////////////////////////
//
// audioport_util_pkg.sv: Resources for testbenches.
//
///////////////////////////////////////////////////////////////////////////////

package audioport_util_pkg;

   import apb_pkg::*;
   import audioport_pkg::*;   
   

`ifndef SYNTHESIS

   localparam real INTERRUPT_LATENCY = 10us;
   const string    FILTER_TAPS_FILE = "input/filter_taps.txt";
   
   function void save_test_parameters(string path);
      int 	   file;
      file = $fopen(path, "w");      
      $fdisplay(file, "-----------------------------------------------------------------------------------------------");
      $fdisplay(file, "DT3 PROJECT 2017: SIMULATION PARAMATER VALUES:");
      $fdisplay(file, "-----------------------------------------------------------------------------------------------");      
      $fdisplay(file, "Clock periods:");
      $fdisplay(file, "        clk %f ns", CLK_PERIOD);
      $fdisplay(file, "        mclk %f ns", MCLK_PERIOD);            
      $fdisplay(file, "DESIGN PARAMETERS:");
      $fdisplay(file, "        FILTER_TAPS                  %10d", FILTER_TAPS);
      $fdisplay(file, "        AUDIO_BUFFER_SIZE            %10d", AUDIO_BUFFER_SIZE);
      $fdisplay(file, "        CMD_WAIT_STATES              %10d", CMD_WAIT_STATES);                  
      $fdisplay(file, "REGISTERS:");
      $fdisplay(file, "        AUDIOPORT_REGISTERS          %10d", AUDIOPORT_REGISTERS);
      $fdisplay(file, "        ABUF_REGISTERS               %10d", ABUF_REGISTERS);
      $fdisplay(file, "INTERNAL REGISTER ADDRESSES (DECIMAL):");
      $fdisplay(file, "        CMD_REG_INT_ADDRESS          %10d", CMD_REG_INT_ADDRESS);
      $fdisplay(file, "        LEVEL_REG_INT_ADDRESS        %10d", LEVEL_REG_INT_ADDRESS);
      $fdisplay(file, "        CFG_REG_INT_ADDRESS          %10d", CFG_REG_INT_ADDRESS);
      $fdisplay(file, "        DSP_REGS_START_INT_ADDRESS   %10d", DSP_REGS_START_INT_ADDRESS);
      $fdisplay(file, "        DSP_REGS_END_INT_ADDRESS     %10d", DSP_REGS_END_INT_ADDRESS);
      $fdisplay(file, "        ABUF0_START_INT_ADDRESS      %10d", ABUF0_START_INT_ADDRESS);
      $fdisplay(file, "        ABUF0_END_INT_ADDRESS        %10d", ABUF0_END_INT_ADDRESS);
      $fdisplay(file, "        ABUF1_START_INT_ADDRESS      %10d", ABUF1_START_INT_ADDRESS);
      $fdisplay(file, "        ABUF1_END_INT_ADDRESS        %10d", ABUF1_END_INT_ADDRESS);
      $fdisplay(file, "REGISTER APB ADDRESSES (HEX):");
      $fdisplay(file, "        CMD_REG_APB_ADDRESS          %10h", CMD_REG_APB_ADDRESS);
      $fdisplay(file, "        LEVEL_REG_APB_ADDRESS        %10h", LEVEL_REG_APB_ADDRESS);
      $fdisplay(file, "        CFG_REG_APB_ADDRESS          %10h", CFG_REG_APB_ADDRESS);
      $fdisplay(file, "        DSP_REGS_START_APB_ADDRESS   %10h", DSP_REGS_START_APB_ADDRESS);
      $fdisplay(file, "        DSP_REGS_END_APB_ADDRESS     %10h", DSP_REGS_END_APB_ADDRESS);
      $fdisplay(file, "        ABUF0_START_APB_ADDRESS      %10h", ABUF0_START_APB_ADDRESS);
      $fdisplay(file, "        ABUF0_END_APB_ADDRESS        %10h", ABUF0_END_APB_ADDRESS);
      $fdisplay(file, "        ABUF1_START_APB_ADDRESS      %10h", ABUF1_START_APB_ADDRESS);
      $fdisplay(file, "        ABUF1_END_APB_ADDRESS        %10h", ABUF1_END_APB_ADDRESS);
      $fdisplay(file, " APB CONFIGURATION (HEX):");
      $fdisplay(file, "        DUT_START_ADDRESS            %10h", DUT_START_ADDRESS);
      $fdisplay(file, "        DUT_END_ADDRESS              %10h", DUT_END_ADDRESS);      
      $fdisplay(file, "        APB_START_ADDRESS            %10h", APB_START_ADDRESS);
      $fdisplay(file, "        APB_END_ADDRESS              %10h", APB_END_ADDRESS);      
      $fdisplay(file, " clk CYCLES PER SAMPLE:");
      $fdisplay(file, "        CLK_DIV_48000                %10d", CLK_DIV_48000);
      $fdisplay(file, "        CLK_DIV_96000                %10d", CLK_DIV_96000);
      $fdisplay(file, "        CLK_DIV_192000               %10d", CLK_DIV_192000);      
      $fdisplay(file, " CDC PARAREMETRS (INT):");
      $fdisplay(file, "        CDC_HANDSHAKER_INTERVAL      %10d", CDC_HANDSHAKER_INTERVAL);
      $fdisplay(file, "        CDC_HANDSHAKER_LATENCY       %10d", CDC_HANDSHAKER_LATENCY);      
      $fdisplay(file, "        CDC_BITSYNC_INTERVAL         %10d", CDC_BITSYNC_INTERVAL);
      $fdisplay(file, "        CDC_BITYNC_LATENCY           %10d", CDC_BITSYNC_LATENCY);      
      $fdisplay(file, "        CDC_PULSESYNC_INTERVAL       %10d", CDC_PULSESYNC_INTERVAL);
      $fdisplay(file, "        CDC_PULSESYNC_LATENCY        %10d", CDC_PULSESYNC_LATENCY);      
      $fdisplay(file, " dsp_unit PARAREMETERS:");
      $fdisplay(file, "        DSP_UNIT_MAX_LATENCY         %10d", DSP_UNIT_MAX_LATENCY);

      $fdisplay(file, "-----------------------------------------------------------------------------------------------");
      $fclose(file);      

   endfunction
   

   localparam logic signed [31:0] COEFF_SCALING = 32'h7fffffff;
   localparam real 		  M_PI = 3.14159265359;
   
   function automatic int read_filter_taps (ref logic [4*FILTER_TAPS-1:0][31:0] dsp_regs);
      begin
	 int file;
	 string line;
	 int 	lines;
	 real coeff;
	 
	 file = $fopen(FILTER_TAPS_FILE, "r");
	 if (file == 0)
    	   begin
	      real B;
	      
	      for (int f = 0; f < 4; ++f)
		begin
		   case (f)
		      0:
			B =0.35;
		     1:
		       B =0.25;
		     2:
		       B =0.15;
		     3:
		       B = 0.05;
		   endcase 

		   for (int i=0; i < FILTER_TAPS; ++i)
		     begin
			int x;
			real sinc;
			x = (i-FILTER_TAPS/2);
			if (x == 0)
			  dsp_regs[f*FILTER_TAPS+i] = 0.5*COEFF_SCALING;
			else
			  dsp_regs[f*FILTER_TAPS+i] = COEFF_SCALING*B*$sin(2*B*M_PI*x)/(2*B*M_PI*x);
		     end
		end
	      
	      return 0;
    	   end

	 lines = 0;
	 
	 while($fgets(line, file) != 0 && lines < 4*FILTER_TAPS)
	   begin
	      if ($sscanf(line, "%f", coeff) != 1)
		$error("Filter tap file format error (expected 1 floating point value)\n");
	      else
		dsp_regs[lines] = ((2**31)-1) * coeff;
	      ++lines;
	   end
	 $fclose(file);
	 return lines;
      end
   endfunction
`endif
   
endpackage
   
