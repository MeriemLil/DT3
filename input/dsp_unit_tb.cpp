#include "dsp_unit_tb.h"
#include <iostream>
#include <iomanip>
using namespace std;
#include <math.h>
extern ofstream output_file;
extern ofstream sox_file;
extern char *input_dir;

#define FILTER_TAPS_FILE  "filter_taps.txt"
#define MAX_AMPLITUDE 8388607
#define COEFF_SCALING 0x7fffffff

int sample_rate = 48000;

// Scaling test constants

#define SCALING_TEST_LENGTH 4800
#define SCALING_TEST_FREQUENCY_L 400.0
#define SCALING_TEST_FREQUENCY_R 800.0
#define SCALING_TEST_AMPLITUDE_L 0.5*MAX_AMPLITUDE
#define SCALING_TEST_AMPLITUDE_R 0.5*MAX_AMPLITUDE


// Input signal amplitude

#define SWEEP_TEST_LENGTH 6000
#define SWEEP_TEST_AMPLITUDE 0.5

void dsp_unit_tb::tx()
{
  sc_int<DATABITS> input_data[2]; 
  sc_time t1;
  int sample_counter;
  int total_samples;
  int latency;
  int simulation_length = 0;
  double left_level = 0;
  double right_level = 1.0;
  sc_uint<16> left_level16 = 0;
  sc_uint<16> right_level16 = 0x1000;
  sc_uint< 32 > level_cfg;

  int sweep_start = 0;
  int counter = 0;
  double phase = 0.0;
  double finc = 0.0;
  double frequency = 0.0;
  double envelope = 0.0;

  ///////////////////////////////////////////////////////////
  // Reset Section
  ///////////////////////////////////////////////////////////

  sample_counter = 0;
  total_samples = 0;

  abuf_in[0].write(0);
  abuf_in[1].write(0);
  tick_in.write(0);
  cfg_in.write(0);
  level_in.write(0);
  clr_in.write(0);
  level_reg_in.write(0x80004000);
  cfg_reg_in.write(0x00000008);

  if (read_filter_taps() != 4*FILTER_TAPS)
    {
      cout << "Using default filter coefficients values" << endl;
    }

  wait();

  ///////////////////////////////////////////////////////////
  // Test 1: Write configuration registers
  ///////////////////////////////////////////////////////////

  SC_REPORT_INFO("", "T1, Write to config registers");

  cfg_reg_in.write(0xffffffff);
  wait(5);

  cfg_in.write(1);
  wait();
  cfg_in.write(0);

  cfg_reg_in.write(0x00000000);
  wait(5);

  cfg_in.write(1);
  wait();
  cfg_in.write(0);

  level_reg_in.write(0xffffffff);

  wait(5);

  level_in.write(1);
  wait();
  level_in.write(0);

  level_reg_in.write(0x00000000);

  wait(5);

  level_in.write(1);
  wait();
  level_in.write(0);

  wait(50);

  ///////////////////////////////////////////////////////////
  // Test 2: Write dsp_regs
  ///////////////////////////////////////////////////////////

  SC_REPORT_INFO("", "T2: Write dsp_regs");

  for(int i=0; i < 4*FILTER_TAPS; ++i)
      {
	dsp_regs_in[i].write(filter_taps[i]);
      }
  
  wait(5);

  cfg_in.write(1);
  wait();
  cfg_in.write(0);

  wait(50);


  ///////////////////////////////////////////////////////////
  // Test 3: Scaling, stereo
  ///////////////////////////////////////////////////////////

  SC_REPORT_INFO("", "T3; Scaling, Stereo, 192KHz");

  level_reg_in.write(0x80000000);

  wait(5);

  level_in.write(1);
  wait();
  level_in.write(0);

  wait(5);

  cfg_reg_in.write(0x00000002); // Filter=Off, Mono=OFF, 192kHz,
  cfg_in.write(1);
  wait();
  cfg_in.write(0);

  wait(20);

  sample_counter = 0;
  sample_rate = 192000;
  phase = 0.0;
  left_level = 0;
  right_level = 1.0;
  left_level16 = 0;
  right_level16 = 0x8000;

  
  while(sample_counter < SCALING_TEST_LENGTH) {
    
    // Generate sine waveforms
    
    phase = (sample_counter * SCALING_TEST_FREQUENCY_L * 2 * M_PI)/ (double)sample_rate;
    input_data[LEFT] = SCALING_TEST_AMPLITUDE_L*sin (phase);
    phase = (sample_counter * SCALING_TEST_FREQUENCY_R * 2 * M_PI)/ (double)sample_rate;
    input_data[RIGHT] = SCALING_TEST_AMPLITUDE_R*sin (phase);
    
    abuf_in[LEFT].write(input_data[LEFT]);
    abuf_in[RIGHT].write(input_data[RIGHT]);
    tick_in.write(1);

    input_samples[LEFT].push(input_data[LEFT]);
    input_samples[RIGHT].push(input_data[RIGHT]);
    ++sample_counter;

    wait();
    tick_in.write(0);	
    t1 = sc_time_stamp();
    start_times.push(t1);

    latency = 0;
    while(0 && valid_out.read() == false)
      {
	wait();
	++latency;
      }
    if (latency < CLK_DIV_192000)
      wait(CLK_DIV_192000-latency);
        
    // Change level scaling
    
    left_level += 1.0/(double)SCALING_TEST_LENGTH;
    right_level -= 1.0/(double)SCALING_TEST_LENGTH;
    left_level16 = 0x8000*left_level;
    right_level16 = 0x8000*right_level;
    level_cfg.range(31,16) = right_level16;
    level_cfg.range(15,0) = left_level16;
    level_reg_in.write(level_cfg);
    level_in.write(1);
    wait();
    level_in.write(0);
    wait();
    
  }

  total_samples += sample_counter;

  wait(50);

  ///////////////////////////////////////////////////////////
  // Test 4: Scaling, mono
  ///////////////////////////////////////////////////////////

  SC_REPORT_INFO("", "T4 Scaling, Mono, 192KHz");

  level_reg_in.write(0x80000002);

  wait(5);

  level_in.write(1);
  wait();
  level_in.write(0);

  wait(5);

  cfg_reg_in.write(0x00000006); // Filter=Off, Mono=ON, 192kHz,
  cfg_in.write(1);
  wait();
  cfg_in.write(0);

  wait(20);

  sample_counter = 0;
  sample_rate = 192000;
  phase = 0.0;
  left_level = 0;
  right_level = 1.0;
  left_level16 = 0;
  right_level16 = 0x8000;

  while(sample_counter < SCALING_TEST_LENGTH) {
    
    // Generate sine waveforms
    
    phase = (sample_counter * SCALING_TEST_FREQUENCY_L * 2 * M_PI)/ (double)sample_rate;
    input_data[LEFT] = SCALING_TEST_AMPLITUDE_L*sin (phase);
    phase = (sample_counter * SCALING_TEST_FREQUENCY_R * 2 * M_PI)/ (double)sample_rate;
    input_data[RIGHT] = SCALING_TEST_AMPLITUDE_R*sin (phase);
    
    abuf_in[LEFT].write(input_data[LEFT]);
    abuf_in[RIGHT].write(input_data[RIGHT]);
    tick_in.write(1);

    input_samples[LEFT].push(input_data[LEFT]);
    input_samples[RIGHT].push(input_data[RIGHT]);
    ++sample_counter;

    wait();
    tick_in.write(0);	
    t1 = sc_time_stamp();
    start_times.push(t1);

    latency = 0;
    while(0 && valid_out.read() == false)
      {
	wait();
	++latency;
      }
    if (latency < CLK_DIV_192000)
      wait(CLK_DIV_192000-latency);

    // Change level scaling
    
    left_level += 1.0/(double)SCALING_TEST_LENGTH;
    right_level -= 1.0/(double)SCALING_TEST_LENGTH;
    left_level16 = 0x8000*left_level;
    right_level16 = 0x8000*right_level;
    level_cfg.range(31,16) = right_level16;
    level_cfg.range(15,0) = left_level16;
    level_reg_in.write(level_cfg);
    level_in.write(1);
    wait();
    level_in.write(0);
    wait();
    
  }

  total_samples += sample_counter;  
  
  wait(50);


  ///////////////////////////////////////////////////////////
  // Test 5: Impulse Response (Stereo)
  ///////////////////////////////////////////////////////////

  SC_REPORT_INFO("", "T5 Filter, Stereo, 192 kHz, Impulse");

  clr_in.write(1);
  wait();
  clr_in.write(0);

  cfg_reg_in.write(0x0000000A);
  wait(5);

  cfg_in.write(1);
  wait();
  cfg_in.write(0);

  level_reg_in.write(0x80008000);

  wait(5);

  level_in.write(1);
  wait();
  level_in.write(0);

  wait(5);

  simulation_length = 3*FILTER_TAPS;
  sample_counter = 0;
  sample_rate = 1920000;

  while(sample_counter < simulation_length)
    {
      
      // Generate input data for next audio processing cycle
    
      if (sample_counter == 0)
	{
	  input_data[LEFT] = 0.95*pow(2, DATABITS-1);
	  input_data[RIGHT] = 0;
	}
      else if (sample_counter < FILTER_TAPS)
	{
	  input_data[LEFT] = 0;
	  input_data[RIGHT] = 0;
	}
      else if (sample_counter == FILTER_TAPS)
	{
	  input_data[LEFT] = 0;
	  input_data[RIGHT] = 0.95*pow(2, DATABITS-1);
	}
      else if (sample_counter < 2*FILTER_TAPS)
	{
	  input_data[LEFT] = 0;
	  input_data[RIGHT] = 0;
	}
      else if (sample_counter == 2*FILTER_TAPS)
	{
	  input_data[LEFT] = 0.95*pow(2, DATABITS-1);
	  input_data[RIGHT] = 0.95*pow(2, DATABITS-1);
	}
      else
	{
	  input_data[LEFT] = 0;
	  input_data[RIGHT] = 0;
	}

    abuf_in[LEFT].write(input_data[LEFT]);
    abuf_in[RIGHT].write(input_data[RIGHT]);
    tick_in.write(1);

    input_samples[LEFT].push(input_data[LEFT]);
    input_samples[RIGHT].push(input_data[RIGHT]);
    ++sample_counter;

    wait();
    tick_in.write(0);
    t1 = sc_time_stamp();
    start_times.push(t1);

    latency = 0;
    while(0 && valid_out.read() == false)
      {
	wait();
	++latency;
      }
    if (latency < CLK_DIV_192000)
      wait(CLK_DIV_192000-latency);
    
  }

  total_samples += sample_counter;
  wait(50);


  ///////////////////////////////////////////////////////////
  // Test 6: Impulse Response (Mono)
  ///////////////////////////////////////////////////////////

  SC_REPORT_INFO("", "T6 Filter, Mono, 192 kHz, Impulse");

  clr_in.write(1);
  wait();
  clr_in.write(0);

  cfg_reg_in.write(0x0000000E);
  wait(5);

  cfg_in.write(1);
  wait();
  cfg_in.write(0);

  level_reg_in.write(0x80008000);

  wait(5);

  level_in.write(1);
  wait();
  level_in.write(0);

  wait(5);

  simulation_length = 3*FILTER_TAPS;
  sample_counter = 0;
  sample_rate = 1920000;

  while(sample_counter < simulation_length)
    {
      
      // Generate input data for next audio processing cycle
    
      if (sample_counter == 0)
	{
	  input_data[LEFT] = 0.95*pow(2, DATABITS-1);
	  input_data[RIGHT] = 0;
	}
      else if (sample_counter < FILTER_TAPS)
	{
	  input_data[LEFT] = 0;
	  input_data[RIGHT] = 0;
	}
      else if (sample_counter == FILTER_TAPS)
	{
	  input_data[LEFT] = 0;
	  input_data[RIGHT] = 0.95*pow(2, DATABITS-1);
	}
      else if (sample_counter < 2*FILTER_TAPS)
	{
	  input_data[LEFT] = 0;
	  input_data[RIGHT] = 0;
	}
      else if (sample_counter == 2*FILTER_TAPS)
	{
	  input_data[LEFT] = 0.95*pow(2, DATABITS-1);
	  input_data[RIGHT] = 0.95*pow(2, DATABITS-1);
	}
      else
	{
	  input_data[LEFT] = 0;
	  input_data[RIGHT] = 0;
	}

    abuf_in[LEFT].write(input_data[LEFT]);
    abuf_in[RIGHT].write(input_data[RIGHT]);
    tick_in.write(1);

    input_samples[LEFT].push(input_data[LEFT]);
    input_samples[RIGHT].push(input_data[RIGHT]);
    ++sample_counter;

    wait();
    tick_in.write(0);
    t1 = sc_time_stamp();
    start_times.push(t1);

    latency = 0;
    while(0 && valid_out.read() == false)
      {
	wait();
	++latency;
      }
    if (latency < CLK_DIV_192000)
      wait(CLK_DIV_192000-latency);
    
  }

  total_samples += sample_counter;
  wait(50);



  ///////////////////////////////////////////////////////////
  // Test 7: Sweep
  ///////////////////////////////////////////////////////////

  SC_REPORT_INFO("", "T7 Filter, Stereo, 192Hz, Sweep");

  clr_in.write(1);
  wait();
  clr_in.write(0);

  simulation_length = SWEEP_TEST_LENGTH;
  sample_counter = 0;
  sample_rate = 192000;

  sweep_start = 0;
  frequency = 1.0;
  finc = (0.25*(double)sample_rate)/((double)simulation_length/3.0);

  cfg_reg_in.write(0x00000000A);
  wait(5);
  cfg_in.write(1);
  wait();
  cfg_in.write(0);

  wait(5);

  level_reg_in.write(0x80008000);

  wait(5);

  level_in.write(1);
  wait();
  level_in.write(0);

  wait(5);


  while(sample_counter < simulation_length)
    {

    // Generate input data for next audio processing cycle
    
      phase = (frequency * 2 * M_PI) *((double)(sample_counter-sweep_start)/ (double)sample_rate);
      switch (counter)
	{
	case 0:
	  input_data[LEFT] = SWEEP_TEST_AMPLITUDE*pow(2, DATABITS-1)*sin (phase);
	  input_data[RIGHT] = 0;
	  break;
	case 1:
	  input_data[LEFT] = 0;
	  input_data[RIGHT] = SWEEP_TEST_AMPLITUDE*pow(2, DATABITS-1)*sin (phase);
	  break;
	case 2:
	  input_data[LEFT] = SWEEP_TEST_AMPLITUDE*pow(2, DATABITS-1)*sin (phase);
	  input_data[RIGHT] = input_data[LEFT];
	  break;
	default:
	  break;
	}
	
      if ((sample_counter - sweep_start) < simulation_length/3)
	{
	  frequency += finc;
	}
      else 
	{
	  frequency = 1.0;
	  sweep_start = sample_counter;
	  counter = counter + 1;
	}
      
      abuf_in[LEFT].write(input_data[LEFT]);
      abuf_in[RIGHT].write(input_data[RIGHT]);
      tick_in.write(1);

      input_samples[LEFT].push(input_data[LEFT]);
      input_samples[RIGHT].push(input_data[RIGHT]);
      ++sample_counter;

      wait();
      tick_in.write(0);
      t1 = sc_time_stamp();
      start_times.push(t1);

    latency = 0;
    while(0 && valid_out.read() == false)
      {
	wait();
	++latency;
      }
    if (latency < CLK_DIV_192000)
      wait(CLK_DIV_192000-latency);

    }

  total_samples += sample_counter;

  wait(50);

  ///////////////////////////////////////////////////////////
  // Test 8: Clear data
  ///////////////////////////////////////////////////////////

  SC_REPORT_INFO("", "T8 Clear");

  clr_in.write(1);
  wait();
  clr_in.write(0);

  sample_counter = 0;
  sample_rate = 192000;

  while(sample_counter < FILTER_TAPS) {
    
    // Generate sine waveforms
    
    input_data[LEFT] = 0;
    input_data[RIGHT] = 0;
    
    abuf_in[LEFT].write(input_data[LEFT]);
    abuf_in[RIGHT].write(input_data[RIGHT]);
    tick_in.write(1);

    input_samples[LEFT].push(input_data[LEFT]);
    input_samples[RIGHT].push(input_data[RIGHT]);
    ++sample_counter;

    wait();
    tick_in.write(0);	
    t1 = sc_time_stamp();
    start_times.push(t1);

    latency = 0;
    while(0 && valid_out.read() == false)
      {
	wait();
	++latency;
      }
    if (latency < CLK_DIV_192000)
      wait(CLK_DIV_192000-latency);
  }

  total_samples += sample_counter;
 
  wait(50);


  sc_stop();
}


void dsp_unit_tb::rx()
{
  sc_time t_CLOCK(CLK_PERIOD, SC_NS);

  sample_number = 0;

  wait();

  while(1) {

    while(valid_out.read() == false)
      wait();

    sc_time& t1 = start_times.front();
    start_times.pop();

    sc_time t2 = sc_time_stamp();    

    sc_int<DATABITS>& input_data_l = input_samples[LEFT].front();
    sc_int<DATABITS>& input_data_r = input_samples[RIGHT].front();
    input_samples[LEFT].pop();
    input_samples[RIGHT].pop();
    
    inputs[LEFT] = input_data_l;
    inputs[RIGHT] = input_data_r;

    outputs[LEFT] = dsp_out[0].read();
    outputs[RIGHT] = dsp_out[1].read();
    
    cout << setw(8) << sample_number;
    cout << setw(10) << inputs[LEFT] << setw(10) << inputs[RIGHT];
    cout << setw(10) << outputs[LEFT] << setw(10) << outputs[RIGHT];    
    cout << "  Latency = " << (t2.to_double()-t1.to_double())/t_CLOCK.to_double();
    cout << endl;
    
    if (output_file.is_open())
      {
	output_file << sample_number;
	output_file << " " << inputs[LEFT] << " " << inputs[RIGHT];
	output_file << " " << outputs[LEFT] << " " << outputs[RIGHT];    
	output_file << endl;
      }
    
#define normalize(val) ((double)val/8388607.0)
    
    if (sox_file.is_open())
      {
	sox_file << (double)sample_number*1.0/(double)sample_rate;
	sox_file << " " << normalize(inputs[LEFT]) << " " << normalize(inputs[RIGHT]);    
	sox_file << " " << normalize(outputs[LEFT]) << " " << normalize(outputs[RIGHT]);    
	sox_file << endl;
      }
    
    wait();
    ++sample_number;
  }
}

int dsp_unit_tb::read_filter_taps()
{
  FILE *file;
  char line[1024];
  int 	lines;
  float coeff;
  int coeff_int;
  char  path[1024];
  sprintf(path, "%s/%s", input_dir, FILTER_TAPS_FILE);
  file = fopen(path, "r");

  if (file == NULL)
    {
      double B;

      for (int f = 0; f < 4; ++f)
	{
	switch (f)
	  {
	  case 0:
	    B =0.35;
	    break;
	  case 1:
	    B =0.25;
	    break;
	  case 2:
	    B =0.15;
	    break;
	  case 3:
	    B = 0.05;
	    break;
	  }
	  for (int i=0; i < FILTER_TAPS; ++i)
	    {
	      int x;
	      double sinc;
	      x = (i-FILTER_TAPS/2);
	      if (x == 0)
		filter_taps[f*FILTER_TAPS+i] = (sc_int<32>)  (0.5*COEFF_SCALING);
	      else
		filter_taps[f*FILTER_TAPS+i] = (sc_int<32>)  (COEFF_SCALING*B*sin(2*B*M_PI*x)/(2*B*M_PI*x));
	    }
	}

      return 0;
    }
  else
    {
      lines = 0;

      while(fgets(line, 1023, file) != 0 && lines < 4*FILTER_TAPS)
	{
	  if (sscanf(line, "%f", &coeff) != 1)
	    cout << "Filter tap file format error (expected 1 floating point value)" << endl;
	  else
	    {
	      coeff_int = (coeff * COEFF_SCALING);
	      filter_taps[lines] = (sc_int<32>) coeff_int;
	    }
	  ++lines;
	}

      fclose(file);
      return lines;
    }
}
