// 1.
#include "dsp_unit.h"

void dsp_unit::dsp_proc()
{
  bool mono_v;
  bool filter_v;
  sc_uint<16> level_v[2];
  
  ///////////////////////////////////////////////////////////
  // Reset Section
  ///////////////////////////////////////////////////////////
  
  // 2.
 RESET_REGION: {
    dsp_out[0].write(0);
    dsp_out[1].write(0);
    valid_out.write(0);
  DATA_RESET_LOOP: for (int i=0; i < FILTER_TAPS; ++i)
      {
	data_r[LEFT][i] = 0;
	data_r[RIGHT][i] = 0;
      }

  RESET_WAIT: wait();
  }
  
  ///////////////////////////////////////////////////////////
  // Processing Loop
  ///////////////////////////////////////////////////////////
  
 PROCESS_LOOP: while(true)
    {
      
      // 3.
    INPUT_REGION: {
	
      INPUT_LOOP: while(true)
	  {

	  INPUT_WAIT: wait();
	    valid_out.write(0);

	    // 4.	    	
	    if (tick_in.read())
	      {
		abuf_in_v[LEFT] = abuf_in[LEFT].read();	  
		abuf_in_v[RIGHT] = abuf_in[RIGHT].read();
		if (cfg_reg_in.read()[CFG_FILTER])
		  filter_v = 1;
		else
		  filter_v = 0;

		if (cfg_reg_r.read()[CFG_MONO] == MODE_MONO)
		  mono_v = 1;
		else
		  mono_v = 0;
		level_v[LEFT] = level_r[LEFT].read();
		level_v[RIGHT] = level_r[RIGHT].read();
		break;
	      }
    
	    // 5.	    
	    if (clr_in.read())
	      {
		dsp_out[0].write(0);
		dsp_out[1].write(0);
		valid_out.write(0);

		// ----- To do: reset variables affected by clk ---------


		// ------------------------------------------------

	      }
	  }
	
      }
      
      // 6.      
    PROCESSING_REGION: {
	
	if (!filter_v)
	  {
	    filtered_v[LEFT] = abuf_in_v[LEFT];
	    filtered_v[RIGHT] = abuf_in_v[RIGHT];
	  }
	else
	  {
	    // ----- To do: add code for filter --------------------

	    // ------------------------------------------------
	  }

	scaled_v[LEFT] = filtered_v[LEFT] * level_v[LEFT];
	scaled_v[LEFT] >>= 15;
	scaled_v[RIGHT] = filtered_v[RIGHT] * level_v[RIGHT];
	scaled_v[RIGHT] >>= 15;
	
	if (mono_v)
	  {
	    // ----- To do: add code for modo mode --------------------

	    // ------------------------------------------------
	  }
	
	dsp_out_v[LEFT] = (sc_int<DATABITS>) scaled_v[LEFT];
	dsp_out_v[RIGHT] = (sc_int<DATABITS>) scaled_v[RIGHT];
      }
      
      // 7.            
    OUTPUT_REGION: {

      OUTPUT_WAIT: wait();	
	valid_out.write(1);
	dsp_out[LEFT].write(dsp_out_v[LEFT]);
	dsp_out[RIGHT].write(dsp_out_v[RIGHT]);
      }
    }
}


// 8.
void dsp_unit::regs_proc()
{
  sc_uint<32>         level_reg;

  if (rst_n.read() == 0)
    {
      cfg_reg_r.write(0);
    COEFF_RESET_LOOP: for (int i=0; i < DSP_REGISTERS; ++i)
	{
	  dsp_regs_r[i].write(0);
	}
      level_r[LEFT].write(0);
      level_r[RIGHT].write(0);
    }
  else
    {
      if (cfg_in.read())
	{
	  cfg_reg_r.write(cfg_reg_in.read());	
	COEFF_WRITE_LOOP: for (int i=0; i < DSP_REGISTERS; ++i)
	    {
	      dsp_regs_r[i].write(dsp_regs_in[i].read());
	    }
	}
      else if (level_in.read())
	{
	  level_reg = level_reg_in.read();
	  level_r[LEFT].write(level_reg.range(15,0).to_uint());
	  level_r[RIGHT].write(level_reg.range(31,16).to_uint());
	}
    }
}


#if defined(MTI_SYSTEMC)
SC_MODULE_EXPORT(dsp_unit);
#endif

