#include "tlm_audioport.h"

// ----------------------------------------------------------------------------------
// b_transport: TLM2.0 blocking transport method for target
// ----------------------------------------------------------------------------------

void tlm_audioport::b_transport( tlm::tlm_generic_payload& trans, sc_time& delay )
{
    tlm_cmd  = trans.get_command();
    tlm_addr = trans.get_address();
    tlm_buffer = trans.get_data_ptr();
    tlm_len  = trans.get_data_length();
    tlm_byt  = trans.get_byte_enable_ptr();
    tlm_wid  = trans.get_streaming_width();
    
    if (tlm_byt != 0 || tlm_len > 4 || tlm_wid < tlm_len)
      SC_REPORT_ERROR("TLM-2", "Target does not support given generic payload transaction format");
    
    if ((tlm_addr < sc_dt::uint64(AUDIOPORT_START_APB_ADDRESS)) || (tlm_addr > sc_dt::uint64(AUDIOPORT_END_APB_ADDRESS)))
      SC_REPORT_ERROR("TLM-2", "Generic payload transaction address out of range");  
    else
      {
	if ( tlm_cmd == tlm::TLM_READ_COMMAND )
	  {
	    bus_read((unsigned int)tlm_addr, tlm_data, delay);
	    memcpy(tlm_buffer, &tlm_data, tlm_len);
	  }
	else if ( tlm_cmd == tlm::TLM_WRITE_COMMAND )
	  {
	    memcpy(&tlm_data, tlm_buffer, tlm_len);
	    bus_write((unsigned int)tlm_addr, tlm_data, delay);
	  }
	trans.set_response_status( tlm::TLM_OK_RESPONSE );
      }
}

// ----------------------------------------------------------------------------------
// bus_read: Register bank read
// ----------------------------------------------------------------------------------

void tlm_audioport::bus_read(unsigned int addr, unsigned int &rdata, sc_time& delay )
{
  sc_time t(TLM_DATA_READ_DELAY, SC_NS);
  addr = (addr - AUDIOPORT_START_APB_ADDRESS)/4;
  rdata = rbank_r[addr];
  delay = t;
}

// ----------------------------------------------------------------------------------
// bus_write: Register bank write and command actions
// ----------------------------------------------------------------------------------

void tlm_audioport::bus_write(unsigned int addr, unsigned int wdata, sc_time& delay )
{
  addr = (addr - AUDIOPORT_START_APB_ADDRESS)/4;
  rbank_r[addr] = wdata;
  
  if (addr == CMD_REG_INT_ADDRESS)
    {
      sc_time t(TLM_COMMAND_WRITE_DELAY, SC_NS);
      delay = t;
      cmd_r = wdata;
      switch (cmd_r.range(31,24))
	{
	case CMD_START:
	  {
	    play_mode = 1;
	    break;
	  }
	case CMD_STOP:
	  {
	    play_mode = 0;	
	    break;
	  }
	case CMD_CFG:
	  {
	    active_config_data = rbank_r[CFG_REG_INT_ADDRESS];
	    for (int i=0; i < DSP_REGISTERS; ++i)
	      active_dsp_regs[i] = rbank_r[DSP_REGS_START_INT_ADDRESS+i];
	    break;
	  }
	case CMD_LEVEL:
	  {
	    active_level_data[0] = rbank_r[LEVEL_REG_INT_ADDRESS].range(15,0);
	    active_level_data[1] = rbank_r[LEVEL_REG_INT_ADDRESS].range(31,16);
	    break;
	  }
	case CMD_CLR:
	  {
	    for(int j=0; j < ABUF_REGISTERS; ++j)
	      rbank_r[ABUF0_START_INT_ADDRESS+j] = 0;
	    for(int j=0; j < FILTER_TAPS; ++j)
	      {
		filter_data[j][0] = 0;
		filter_data[j][1] = 0;		
	      }
	    abuf_read_counter = 0;
	    dsp_inputs[0] = 0;
	    dsp_inputs[1] = 0;
	    dsp_outputs[0] = 0;
	    dsp_outputs[1] = 0;
	    audio_data_t tmp;
	    while (buffer_fifo.nb_read(tmp)); // clear fifo!
	    break;
	  }
	}
    }
  else
    {
      sc_time t(TLM_DATA_WRITE_DELAY, SC_NS);
      delay = t;
    }
  if (addr >= ABUF0_START_INT_ADDRESS && addr <= ABUF1_END_INT_ADDRESS)
    irq = 0;
}

// ----------------------------------------------------------------------------------
// do_dsp: DSP thread
// ----------------------------------------------------------------------------------

void tlm_audioport::do_dsp()
{

  while(1)
    {
      wait(req);
      
      if ((abuf_read_counter == 2*AUDIO_BUFFER_SIZE-2) || 
	  (abuf_read_counter == 4*AUDIO_BUFFER_SIZE-2)) 
	irq = 1;
      
      dsp_inputs[0] = rbank_r[ABUF0_START_INT_ADDRESS+abuf_read_counter];
      abuf_read_counter = abuf_read_counter + 1;
      dsp_inputs[1] = rbank_r[ABUF0_START_INT_ADDRESS+abuf_read_counter];
      abuf_read_counter = abuf_read_counter + 1;
      
      if (abuf_read_counter >= 4*AUDIO_BUFFER_SIZE-1)
	abuf_read_counter = 0;
      
      // Filter

      if (active_config_data[CFG_FILTER] == 1)
	{
	  for (int tap=FILTER_TAPS-1; tap > 0; --tap)
	    {
	      filter_data[tap][0] = filter_data[tap-1][0];
	      filter_data[tap][1] = filter_data[tap-1][1];			  
	    }
	  filter_data[0][0] = dsp_inputs[0];
	  filter_data[0][1] = dsp_inputs[1];
	  
	  accu30L = 0;
	  accu330L = 0;
	  accu30R = 0;
	  accu330R = 0;
	  
	  for (int tap=0; tap < FILTER_TAPS; ++tap)
	    {
	      sc_int < 24 >                   d;
	      sc_int < 32 >                   c;      
	      sc_int < 32+24 > mul;
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
	    }
	  
	  sumL = accu30L + accu330R;
	  sumR = accu30R + accu330L;
	  sumL = (sumL >> 31);
	  sumR = (sumR >> 31);	   
	  filter_outputs[0] = sumL;
	  filter_outputs[1] = sumR;
	}
      else
	{
	  filter_outputs[0] = dsp_inputs[0];
	  filter_outputs[1] = dsp_inputs[1];
	}
      
      // scaler
      
      scaledL = filter_outputs[0];
      scaledR = filter_outputs[1];
      levelL = 0;
      levelR = 0;
      levelL = (sc_int<17>)(active_level_data[0]);
      levelR = (sc_int<17>)(active_level_data[1]);
      
      scaledL = scaledL * levelL;
      scaledR = scaledR * levelR;		
      scaledL = scaledL >> 15;
      scaledR = scaledR >> 15;		
      
      if (active_config_data[CFG_MONO] == 0)
	{
	  dsp_outputs[0] = scaledL;
	  dsp_outputs[1] = scaledR;
	}
      else
	{
	  scaledR = scaledR >> 1;
	  scaledL = scaledL >> 1;	   
	  dsp_outputs[0] = (scaledL + scaledR);
	  dsp_outputs[1] = dsp_outputs[0];
	}
      
      audio_data_t sample;
      sample.left = dsp_outputs[0];
      sample.right = dsp_outputs[1];
      dsp_data.write(sample);

      wait(TLM_DSP_DELAY, SC_NS);

      tick.notify(TLM_TICK_DELAY, SC_NS);

    }
}


// ----------------------------------------------------------------------------------
// do_i2s: I2S thread
// ----------------------------------------------------------------------------------

void tlm_audioport::do_i2s()
{
  double delay;
  sdo_out.write(0);
  sck_out.write(0);
  ws_out.write(0);
  irq_out.write(0);
  i2s_state = STOP;
  i2s_srg = 0;
  i2s_sample.left = 0;
  i2s_sample.right = 0;
  sck_ctr = 0;
  ws_ctr = 0;
  ws_state = 0;

  while(1)
    {

      if (play_mode && i2s_state == STOP)
	{
	  for(int i=0; i < FIFO_SIZE; ++i)
	    {
	      req.notify(TLM_REQ_DELAY, SC_NS);
	      wait(tick);
	    }
	  i2s_state = PLAY;
	}

      if (!play_mode && sck_ctr == 1 && ws_ctr == 0)
	{
	  while(buffer_fifo.num_available() > 0) // flush fifo
	    buffer_fifo.read();	    
	  i2s_state = STOP;
	}
      if (i2s_state == PLAY)
	{
	  
	  if( sck_ctr == 1)
	    {
	      if (ws_ctr == 0)
		{
		  if (buffer_fifo.num_available() == 0)
		    {
		      SC_REPORT_ERROR("tlm_audioport", "Audio FIFO empty.");
		      sc_stop();
		    }
		  i2s_sample = buffer_fifo.read();
		  req.notify(TLM_REQ_DELAY, SC_NS);
		  i2s_srg = (i2s_sample.left, i2s_sample.right);
		}
	      else
		{
		  i2s_srg = i2s_srg << 1;
		}
	      if (ws_ctr == 23 || ws_ctr == 47)
		ws_state = !ws_state;
	      sdo_out.write(i2s_srg[47]);
	      irq_out.write(irq);
	      ws_out.write(ws_state);
	      sck_out.write(0);
	    }
	  else
	    {
	      sck_out.write(1);
	    }
	  
	  if (sck_ctr == 1)
	    {
	      if (ws_ctr < 47)
		ws_ctr = ws_ctr + 1;
	      else
		ws_ctr = 0;
	    }

	  if (sck_ctr == 0)
	    sck_ctr = 1;
	  else
	    sck_ctr = 0;
	  
	  switch (active_config_data.range(1,0))
	    { 
	    case RATE_48000:
	      {
		delay = 0.02083333/96;
		break;
	      }
	    case RATE_96000:
	      {
		delay = 0.01041666/96;
		break;
	      }
	    case RATE_192000:
	      {
		delay = 0.005208331/96;
		break;
	      }
	    default:
	      {
		SC_REPORT_ERROR("tlm_audioport", "Illegal sample rate");
		sc_stop();
	      }
	    }
	  wait(delay, SC_MS);
	}
      else
	{
	  sdo_out.write(0);
	  sck_out.write(0);
	  ws_out.write(0);
	  i2s_state = STOP;
	  sck_ctr = 0;
	  ws_ctr = 0;
	  ws_state = 0;
	  wait(10.0, SC_NS);
	  irq_out.write(0);
	}
    }
}

// ----------------------------------------------------------------------------------
// do_fifo: I2S input buffer
// ----------------------------------------------------------------------------------

void tlm_audioport::do_fifo()
{
  audio_data_t sample;

  while(1)
    {
      if (play_mode)
	{
	  wait(tick);
	  sample = dsp_data.read();
	  buffer_fifo.write(sample);
	}
      else
	{
	  wait(10.0, SC_NS);
	}
    }
}

#if defined(MTI_SYSTEMC)
SC_MODULE_EXPORT(tlm_audioport);
#endif
