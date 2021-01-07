#include "tlm_top.h"

// Directory from where data are read
char *input_dir = (char *) "input";

// Directory where results files are saved
char *output_dir = (char *) "output";

// Name of simulation tun
char *run_name = (char *) 0;

// Output data file
ofstream output_file;

/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemC sc_main
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

int sc_main( int argc, char *argv[] )
{
  tlm_top *tlm_top_inst;
  char filename[1024];

  sc_set_time_resolution(1,SC_PS);  

  tlm_top_inst = new tlm_top("tlm_top_inst");
  for (int i=1; i < argc; ++i)
    {
      if (!strcmp(argv[i], "-run"))
	{
	  ++i;
	  if (i < argc) run_name = argv[i];
	}
      else if (!strcmp(argv[i], "-input"))
	{
	  ++i;
	  if (i < argc) input_dir = argv[i];
	}
      else if (!strcmp(argv[i], "-output"))
	{
	  ++i;
	  if (i < argc) output_dir = argv[i];

	}
    }

  sprintf(filename, "%s/tlm_audioport_%s_out.txt", output_dir, run_name);
  output_file.open(filename);
  
  if (!output_file.is_open())
    cout << "Unable to open simulation output file " << filename << endl;
  else
    cout << "Simulation output is saved to file " << filename << endl;

  sc_start();

  cout << "SIMULATION STOPPED AT TIME = " << sc_time_stamp() << endl;

  if (output_file.is_open())
    output_file.close();

  return 0;  
}
