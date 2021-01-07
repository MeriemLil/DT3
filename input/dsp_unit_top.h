#ifndef dsp_unit_top_h
#define dsp_unit_top_h

// 1.

#include "dsp_unit.h"
#include "dsp_unit_tb.h"

#ifdef STRATUS_HLS
#include "../output/dsp_unit_stratus_work/wrappers/dsp_unit_wrap.h"
#endif

// 2.
SC_MODULE(dsp_unit_top) {
  sc_clock clk;
  sc_signal<bool> rst_n;
  sc_signal < sc_int<DATABITS> > abuf_in[2];
  sc_signal < bool > tick_in;
  sc_signal < bool > cfg_in;
  sc_signal < bool > level_in;
  sc_signal < bool > clr_in;
  sc_signal < sc_int<32> > dsp_regs_in[DSP_REGISTERS];
  sc_signal  < sc_uint<32> > cfg_reg_in;
  sc_signal  < sc_uint<32> > level_reg_in;
  sc_signal < sc_int<DATABITS> > dsp_out[2];
  sc_signal < bool > valid_out;

#if defined STRATUS_HLS
  dsp_unit_wrapper dsp_unit_inst;
#else
  dsp_unit dsp_unit_inst; 
#endif

  dsp_unit_tb dsp_unit_tb_inst;

  void reset_thread();

 SC_CTOR(dsp_unit_top) :
  clk("clk", CLK_PERIOD, SC_NS, 0.5),
#ifndef HLS_RTL
    dsp_unit_inst("dsp_unit_inst"),
#else
    dsp_unit_inst("dsp_unit_inst", "work.dsp_unit"),
#endif

    dsp_unit_tb_inst("dsp_unit_tb_inst")    
  {
    SC_THREAD(reset_thread);
    dont_initialize();
    sensitive << clk.posedge_event();


  dsp_unit_inst.clk(clk);
  dsp_unit_inst.rst_n(rst_n);
  dsp_unit_inst.abuf_in[1](abuf_in[1]);
  dsp_unit_inst.abuf_in[0](abuf_in[0]);
  dsp_unit_inst.tick_in(tick_in);
  dsp_unit_inst.cfg_in(cfg_in);
  dsp_unit_inst.level_in(level_in);
  dsp_unit_inst.clr_in(clr_in);
  dsp_unit_inst.cfg_reg_in(cfg_reg_in);
  dsp_unit_inst.level_reg_in(level_reg_in);
  dsp_unit_inst.dsp_out[0](dsp_out[0]);
  dsp_unit_inst.dsp_out[1](dsp_out[1]);
  dsp_unit_inst.valid_out(valid_out);

  for (int i=0; i < DSP_REGISTERS; ++i)
      dsp_unit_inst.dsp_regs_in[i](dsp_regs_in[i]);

  dsp_unit_tb_inst.clk(clk);
  dsp_unit_tb_inst.rst_n(rst_n);
  dsp_unit_tb_inst.abuf_in[0](abuf_in[0]);
  dsp_unit_tb_inst.abuf_in[1](abuf_in[1]);
  dsp_unit_tb_inst.tick_in(tick_in);
  dsp_unit_tb_inst.cfg_in(cfg_in);
  dsp_unit_tb_inst.level_in(level_in);
  dsp_unit_tb_inst.clr_in(clr_in);
  dsp_unit_tb_inst.cfg_reg_in(cfg_reg_in);
  dsp_unit_tb_inst.level_reg_in(level_reg_in);
  dsp_unit_tb_inst.dsp_out[0](dsp_out[0]);
  dsp_unit_tb_inst.dsp_out[1](dsp_out[1]);
  dsp_unit_tb_inst.valid_out(valid_out);

  for (int i=0; i < DSP_REGISTERS; ++i)
    dsp_unit_tb_inst.dsp_regs_in[i](dsp_regs_in[i]);
  }

};

#endif
