#ifndef audioport_defs_h
#define audioport_defs_h

// Design parameters

//////////////////////////////////////////////////////////////////
//
// 1. Project parameters
//
//////////////////////////////////////////////////////////////////

#define CLK_PERIOD          17.5
#define MCLK_PERIOD         54.25347222
#define FILTER_TAPS         47
#define AUDIO_BUFFER_SIZE   42
#define CMD_WAIT_STATES     25

//////////////////////////////////////////////////////////////////
//
// 2. Register counts for address computation
//
//////////////////////////////////////////////////////////////////

#define DSP_REGISTERS       (4*FILTER_TAPS)
#define ABUF_REGISTERS      (4*AUDIO_BUFFER_SIZE)
#define AUDIOPORT_REGISTERS (3+DSP_REGISTERS+ABUF_REGISTERS)

//////////////////////////////////////////////////////////////////
//
// 3. Register addresses in internal address (int_addr) memory space
//
//////////////////////////////////////////////////////////////////

#define INT_ADDR_BITS               9
#define CMD_REG_INT_ADDRESS         0
#define LEVEL_REG_INT_ADDRESS       1
#define CFG_REG_INT_ADDRESS         2
#define DSP_REGS_START_INT_ADDRESS  3
#define DSP_REGS_END_INT_ADDRESS    (DSP_REGS_START_INT_ADDRESS + DSP_REGISTERS - 1)   
#define ABUF0_START_INT_ADDRESS     (DSP_REGS_END_INT_ADDRESS + 1)
#define ABUF0_END_INT_ADDRESS       (ABUF0_START_INT_ADDRESS + 2*AUDIO_BUFFER_SIZE-1)
#define ABUF1_START_INT_ADDRESS     (ABUF0_START_INT_ADDRESS + 2*AUDIO_BUFFER_SIZE)
#define ABUF1_END_INT_ADDRESS       (ABUF0_START_INT_ADDRESS + 4*AUDIO_BUFFER_SIZE-1) 
   
//////////////////////////////////////////////////////////////////
//
// 4. Register addresses in APB address spaces
//
//////////////////////////////////////////////////////////////////   

#define AUDIOPORT_START_APB_ADDRESS  0x8c000000   
#define AUDIOPORT_END_APB_ADDRESS    (AUDIOPORT_START_APB_ADDRESS + (AUDIOPORT_REGISTERS-1)*4)
#define CMD_REG_APB_ADDRESS          (AUDIOPORT_START_APB_ADDRESS)
#define LEVEL_REG_APB_ADDRESS        (AUDIOPORT_START_APB_ADDRESS + 4)
#define CFG_REG_APB_ADDRESS          (AUDIOPORT_START_APB_ADDRESS + 8)
#define DSP_REGS_START_APB_ADDRESS   (AUDIOPORT_START_APB_ADDRESS + 12)
#define DSP_REGS_END_APB_ADDRESS     (DSP_REGS_START_APB_ADDRESS + (DSP_REGISTERS-1)*4)
#define ABUF_START_APB_ADDRESS       (DSP_REGS_END_APB_ADDRESS + 4)
#define ABUF_END_APB_ADDRESS         (ABUF_START_APB_ADDRESS + (ABUF_REGISTERS-1)*4)
#define ABUF0_START_APB_ADDRESS      (DSP_REGS_END_APB_ADDRESS + 4)
#define ABUF0_END_APB_ADDRESS        (ABUF0_START_APB_ADDRESS + (AUDIO_BUFFER_SIZE*2-1)*4)
#define ABUF1_START_APB_ADDRESS      (ABUF0_END_APB_ADDRESS+4)
#define ABUF1_END_APB_ADDRESS        (ABUF1_START_APB_ADDRESS + (AUDIO_BUFFER_SIZE*2-1)*4)

//////////////////////////////////////////////////////////////////
//
// 5. Constants
//
//////////////////////////////////////////////////////////////////   

#define CMD_NOP          0x0
#define CMD_CLR          0x1
#define CMD_CFG          0x2
#define CMD_START        0x4
#define CMD_STOP         0x8
#define CMD_LEVEL        0x10   

// b: Configuration register CFG_REG   

// Configuration bit indices

#define CFG_MONO      2
#define CFG_FILTER    3

// Names of configuration bit values

#define MODE_MONO     1
#define MODE_STEREO   0
#define RATE_48000    0
#define RATE_96000    1
#define RATE_192000   2

// c: Constants used in dsp_unit

#define DATABITS      24
#define COEFFBITS     32
#define LEFT          0
#define RIGHT         1
#define ACCBITS       32
#define SUMBITS       32

// d: These are needed in the testbench

#define CLK_DIV_48000        ((1000000000.0/48000.0)/(CLK_PERIOD))
#define CLK_DIV_96000        ((1000000000.0/96000.0)/(CLK_PERIOD))
#define CLK_DIV_192000       ((1000000000.0/192000.0)/(CLK_PERIOD))

#define FIFO_SIZE    4

#endif
