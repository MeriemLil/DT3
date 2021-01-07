#ifndef tlm_audioport_h
#define tlm_audioport_h


#define SC_INCLUDE_DYNAMIC_PROCESSES
#define SC_INCLUDE_FX
#include <systemc.h>
#include "tlm.h"
#include "tlm_utils/simple_target_socket.h"
#include <queue>

using namespace sc_core;
using namespace sc_dt;
using namespace std;

#include "audioport_defs.h"
#include "tlm_audioport_defs.h"

SC_MODULE(tlm_audioport) 
{

  // Ports
  tlm_utils::simple_target_socket<tlm_audioport> socket;    // TLM-2 socket
  sc_out < bool >  irq_out;
  sc_out <bool>    sdo_out;
  sc_out <bool>    ws_out;
  sc_out <bool>    sck_out;

  // TLM variable
  tlm::tlm_command tlm_cmd;
  sc_dt::uint64    tlm_addr;
  unsigned char*   tlm_buffer;
  unsigned int     tlm_len;
  unsigned char*   tlm_byt;
  unsigned int     tlm_wid;
  unsigned int     tlm_data;

  // Registers
  sc_uint< 32 >     cmd_r;
  sc_uint< 32 >     rbank_r [AUDIOPORT_REGISTERS];   
  int 		    abuf_read_counter;
  bool 		    play_mode;
  bool              irq;

  // config register(s) loaded with CMD_CFG command  
  sc_int  < 32 >    active_dsp_regs[DSP_REGISTERS];
  sc_uint < 16 >    active_level_data[2];
  sc_uint < 32 >    active_config_data;            
  
   // dsp_unit filter and output registers
  sc_int < 24>     filter_data[FILTER_TAPS][2];
  sc_bigint < 32+24+FILTER_TAPS >    accu30L, accu330L, accu30R, accu330R;
  sc_bigint < 32+24+FILTER_TAPS+1 >  sumL, sumR;	   
  sc_int < 17 >     levelL;
  sc_int < 17 >     levelR;
  sc_int < 42 >     scaledL;
  sc_int < 42 >     scaledR;
  sc_int < 24 >     dsp_inputs[2];         
  sc_int < 24 >     filter_outputs[2];
  sc_int < 24 >     dsp_outputs[2];      
   
   // I2C waveform generation
   audio_data_t       i2s_sample;
   enum { STOP, PLAY} i2s_state;
   sc_uint<48>        i2s_srg;
   sc_uint<1>         sck_ctr;
   sc_uint<7>         ws_ctr;
   bool               ws_state;

   void b_transport( tlm::tlm_generic_payload& trans, sc_time& delay );
   void bus_write(unsigned int addr, unsigned int wdata, sc_time& delay );
   void bus_read(unsigned int addr, unsigned int &rdata, sc_time& delay );
   void do_dsp();
   void do_fifo();
   void do_i2s();

   sc_event                   req;
   sc_event                   tick;
   sc_signal < audio_data_t > dsp_data;
   sc_fifo < audio_data_t >   buffer_fifo;

 SC_CTOR(tlm_audioport)
   : socket("socket"),
     req("req"),
     tick("tick"),
     buffer_fifo(FIFO_SIZE)
     {
       SC_THREAD(do_dsp);
       SC_THREAD(do_fifo);
       SC_THREAD(do_i2s);
       socket.register_b_transport(this, &tlm_audioport::b_transport);
       irq = 0;
       play_mode = 0;
       abuf_read_counter = 0;
     }
   
   
};


#endif
