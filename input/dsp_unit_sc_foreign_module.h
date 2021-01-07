#ifndef _dsp_unit_sc_foreign_module_
#define _dsp_unit_sc_foreign_module_

class dsp_unit : public sc_foreign_module
{
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

    dsp_unit(sc_module_name nm, const char* hdl_name)
      : sc_foreign_module(nm),
      clk("clk"),
      rst_n("rst_n"),
      tick_in("tick_in"),
      cfg_in("cfg_in"),
      clr_in("clr_in")
	{
	  
	  elaborate_foreign_module(hdl_name);
	}
    ~dsp_unit()
    {}

};

#endif

