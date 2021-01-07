`include "audioport.svh"

package audioport_pkg;

   //////////////////////////////////////////////////////////////////
   //
   // 1. Project parameters
   //
   //////////////////////////////////////////////////////////////////

`ifndef SYNTHESIS
   localparam real CLK_PERIOD       = 17.5;
   localparam real MCLK_PERIOD      = 54.25347222; // Same for all students
`endif
   localparam int FILTER_TAPS          = 31;
   localparam int AUDIO_BUFFER_SIZE    = 32;
   localparam int CMD_WAIT_STATES      = 25; // Set manually to 6 + int'($ceil(6.0*MCLK_PERIOD/CLK_PERIOD)

   //////////////////////////////////////////////////////////////////
   //
   // 2. Register counts for address computation
   //
   //////////////////////////////////////////////////////////////////
   
   // Number of coefficient registers for four FIR filters
   localparam int DSP_REGISTERS    = 4*FILTER_TAPS;

   // Number of 24-bit registers in abuf bank (ABUF0 and ABUF1, both AUDIO_BUFFER_SIZE * 2) + counter register
   localparam int ABUF_REGISTERS = 4*AUDIO_BUFFER_SIZE;

   // Total number of registers
   localparam int AUDIOPORT_REGISTERS = 3 + DSP_REGISTERS + ABUF_REGISTERS;

   //////////////////////////////////////////////////////////////////
   //
   // 3. Register addresses in internal address (int_addr) memory space
   //
   //////////////////////////////////////////////////////////////////

   localparam int INT_ADDR_BITS = $clog2(AUDIOPORT_REGISTERS);
   localparam int CMD_REG_INT_ADDRESS = 0;
   localparam int LEVEL_REG_INT_ADDRESS = 1;
   localparam int CFG_REG_INT_ADDRESS = 2;
   localparam int DSP_REGS_START_INT_ADDRESS = 3;
   localparam int DSP_REGS_END_INT_ADDRESS = DSP_REGS_START_INT_ADDRESS + DSP_REGISTERS - 1;   
   localparam int ABUF0_START_INT_ADDRESS = DSP_REGS_END_INT_ADDRESS + 1;
   localparam int ABUF0_END_INT_ADDRESS = ABUF0_START_INT_ADDRESS + 2*AUDIO_BUFFER_SIZE-1;
   localparam int ABUF1_START_INT_ADDRESS = ABUF0_START_INT_ADDRESS + 2*AUDIO_BUFFER_SIZE;
   localparam int ABUF1_END_INT_ADDRESS = ABUF0_START_INT_ADDRESS + 4*AUDIO_BUFFER_SIZE-1; 
   
   //////////////////////////////////////////////////////////////////
   //
   // 4. Register addresses in APB address spaces
   //
   //////////////////////////////////////////////////////////////////   

   localparam logic [31:0]  AUDIOPORT_START_APB_ADDRESS  = 32'h8c000000;   
   localparam logic [31:0]  AUDIOPORT_END_APB_ADDRESS    = AUDIOPORT_START_APB_ADDRESS + (AUDIOPORT_REGISTERS-1)*4;
   localparam logic [31:0]  CMD_REG_APB_ADDRESS          = AUDIOPORT_START_APB_ADDRESS;
   localparam logic [31:0]  LEVEL_REG_APB_ADDRESS        = AUDIOPORT_START_APB_ADDRESS + 4;
   localparam logic [31:0]  CFG_REG_APB_ADDRESS          = AUDIOPORT_START_APB_ADDRESS + 8;
   localparam logic [31:0]  DSP_REGS_START_APB_ADDRESS   = AUDIOPORT_START_APB_ADDRESS + 12;
   localparam logic [31:0]  DSP_REGS_END_APB_ADDRESS     = DSP_REGS_START_APB_ADDRESS + (DSP_REGISTERS-1)*4;
   localparam logic [31:0]  ABUF_START_APB_ADDRESS       = DSP_REGS_END_APB_ADDRESS + 4;
   localparam logic [31:0]  ABUF_END_APB_ADDRESS         = ABUF_START_APB_ADDRESS + (ABUF_REGISTERS-1)*4;
   localparam logic [31:0]  ABUF0_START_APB_ADDRESS      = DSP_REGS_END_APB_ADDRESS + 4;
   localparam logic [31:0]  ABUF0_END_APB_ADDRESS        = ABUF0_START_APB_ADDRESS + (AUDIO_BUFFER_SIZE*2-1)*4;
   localparam logic [31:0]  ABUF1_START_APB_ADDRESS      = ABUF0_END_APB_ADDRESS+4;
   localparam logic [31:0]  ABUF1_END_APB_ADDRESS        = ABUF1_START_APB_ADDRESS + (AUDIO_BUFFER_SIZE*2-1)*4;
   
   //////////////////////////////////////////////////////////////////
   //
   // 5. Useful Constants
   //
   //////////////////////////////////////////////////////////////////   

   //----------------------------------------------------------------
   // a: Command register CMD_REG
   //----------------------------------------------------------------
   
   // Command codes (one-hot encoded)    
   localparam logic [7:0]  CMD_NOP =          8'h00;
   localparam logic [7:0]  CMD_CLR =          8'h01;
   localparam logic [7:0]  CMD_CFG =          8'h02;
   localparam logic [7:0]  CMD_START =        8'h04;
   localparam logic [7:0]  CMD_STOP =         8'h08;
   localparam logic [7:0]  CMD_LEVEL =        8'h10;   

   // Command bit indices
   localparam int 	   CMD_REG_CLR = 24;
   localparam int 	   CMD_REG_CFG = 25;
   localparam int 	   CMD_REG_START = 26;
   localparam int 	   CMD_REG_STOP = 27;
   localparam int 	   CMD_REG_LEVEL = 28;

   //----------------------------------------------------------------   
   // b: Configuration register CFG_REG   
   //----------------------------------------------------------------
   //    
   // Configuration bit indices
   localparam int 	    CFG_MONO = 2;
   localparam int 	    CFG_FILTER = 3;
   
   // Names of configuration bit values
   localparam logic        FILTER_ENABLED =   1'b1;
   localparam logic        FILTER_DISABLED =  1'b0;
   localparam logic        MODE_MONO =        1'b1;
   localparam logic        MODE_STEREO =      1'b0;   
   localparam logic [1:0]  RATE_48000 =       0;
   localparam logic [1:0]  RATE_96000 =       1;
   localparam logic [1:0]  RATE_192000 =      2;

   //----------------------------------------------------------------   
   // c: Clock divider rations (clk cycles per sample)
   //----------------------------------------------------------------   

`ifndef SYNTHESIS   
   localparam logic [31:0] CLK_DIV_48000 =        int'($ceil((1000000000.0/48000.0)/(CLK_PERIOD)));
   localparam logic [31:0] CLK_DIV_96000 =        int'($ceil((1000000000.0/96000.0)/(CLK_PERIOD)));
   localparam logic [31:0] CLK_DIV_192000 =       int'($ceil((1000000000.0/192000.0)/(CLK_PERIOD)));
`endif
   
   //----------------------------------------------------------------      
   // d: Clock divider ratios for I2S interface (same for all students)
   //----------------------------------------------------------------
   
   localparam logic [31:0]  MCLK_DIV_48000 =        8;
   localparam logic [31:0]  MCLK_DIV_96000 =        4;
   localparam logic [31:0]  MCLK_DIV_192000 =       2;

   //----------------------------------------------------------------   
   // e: cdc_unit verification settings
   //----------------------------------------------------------------   

`ifndef SYNTHESIS
   localparam int 	    CDC_HANDSHAKER_INTERVAL   = 6 + int'($ceil(6.0*MCLK_PERIOD/CLK_PERIOD)); // in clk cycles
   localparam int 	    CDC_HANDSHAKER_LATENCY    = 6 + int'($ceil(3.0*MCLK_PERIOD/CLK_PERIOD)); // in mclk cycles
   localparam int 	    CDC_BITSYNC_INTERVAL      = int'($ceil(MCLK_PERIOD/CLK_PERIOD)); // in clk cycles
   localparam int 	    CDC_BITSYNC_LATENCY       = 2;  // in mclk cycles 
   localparam int 	    CDC_PULSESYNC_INTERVAL    = 1;  // in mclk cycles
   localparam int 	    CDC_PULSESYNC_LATENCY     = 2+int'($ceil(MCLK_PERIOD/CLK_PERIOD)); // in clk cycles
`endif

   //----------------------------------------------------------------      
   // f: i2s_unit FIFO size
   //----------------------------------------------------------------   

   localparam int 	    FIFO_SIZE = 4;

   //----------------------------------------------------------------      
   // 6: dsp_unit max latency
   //----------------------------------------------------------------   

`ifndef SYNTHESIS
   localparam int 	    DSP_UNIT_SHAFETY_MARGIN = 5;
   localparam int 	    DSP_UNIT_MAX_LATENCY = CLK_DIV_192000 - 
                                                   (CDC_PULSESYNC_LATENCY + CDC_HANDSHAKER_INTERVAL) - 
                                                   DSP_UNIT_SHAFETY_MARGIN;
`endif
   
endpackage
   
