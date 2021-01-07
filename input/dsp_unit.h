#ifndef dsp_unit_h
#define dsp_unit_h

#define DONE

// 1. 
#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "dsp_unit_sc_foreign_module.h"
#else

// 2. 
SC_MODULE(dsp_unit) {

  // 3. 
 public:
    sc_in_clk  clk;
    sc_in<bool>  rst_n;
    sc_in < sc_int<DATABITS> > abuf_in[2];
    sc_in < bool > tick_in;
    sc_in < bool > cfg_in;
    sc_in < bool > clr_in;
    sc_in < bool > level_in;
    sc_in  < sc_uint<32> > cfg_reg_in;
    sc_in  < sc_uint<32> > level_reg_in;
    sc_in < sc_int<32> > dsp_regs_in[DSP_REGISTERS];
    sc_out < sc_int<DATABITS> > dsp_out[2];
    sc_out < bool > valid_out;

    // 4.   
    void dsp_proc();
    void regs_proc();
    
    SC_CTOR(dsp_unit) {
      SC_CTHREAD(dsp_proc, clk.pos());
      async_reset_signal_is(rst_n, false);
      
      // Sequential SC_METHOD:
      SC_METHOD(regs_proc);
      sensitive << clk.pos() << rst_n.neg();
      dont_initialize();
    }
    
    // 5.
 private:
    sc_signal < sc_uint<32> > cfg_reg_r;
    sc_signal < sc_int<32> >  dsp_regs_r[DSP_REGISTERS];
    sc_int<DATABITS> data_r[2][FILTER_TAPS];
    sc_signal < sc_uint<16> > level_r[2];

    // ----- To do: Add variables to store coeffs, data, accus, sums -----


    // ---------------------------------------------------------------

  sc_int<DATABITS>    abuf_in_v[2];
  sc_int<DATABITS>    filtered_v[2];
  sc_int<DATABITS+16> scaled_v[2];
  sc_int<DATABITS>    dsp_out_v[2];

};


#endif

#endif
