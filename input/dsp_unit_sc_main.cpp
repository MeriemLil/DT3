#include "dsp_unit_top.h"

// Pointer to top-level SystemC model
dsp_unit_top *stratus_dsp_unit_top_inst = NULL;

// Directory from where data are read
char *input_dir = (char *) "input";

// Directory where results files are saved
char *output_dir = (char *) "output";

// Name of simulation tun
char *run_name = (char *) 0;

// Output data file
ofstream output_file;

// SoX format audio data file
ofstream sox_file;

// Function that opens output files

void open_results_files(char * run_name, char *directory)
{
  char filename[1024];

  if (run_name != NULL)
    {
      sprintf(filename, "%s/dsp_unit_%s_out.txt", directory, run_name);
      output_file.open(filename);
      
      if (!output_file.is_open())
	cout << "Unable to open simulation output file " << filename << endl;
      else
	cout << "Simulation output is saved to file " << filename << endl;

      sprintf(filename, "%s/dsp_unit_%s_out.dat", directory, run_name);
      sox_file.open(filename);
      
      if (!sox_file.is_open())
	cout << "Unable to open simulation output SoX file " << filename << endl;
      else
	cout << "Simulation output is saved in SoX format to file " << filename << endl;
      
      if (sox_file.is_open())
	{
	  sox_file << "; Sample Rate 48000"  << endl;
	  sox_file << "; Channels 4"  << endl;
	}
    }
}

// Function that closes output files
void close_results_files()
{
  if (output_file.is_open())
    output_file.close();
  
  if (sox_file.is_open())
    sox_file.close();
}


/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemC sc_main
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

int sc_main( int argc, char *argv[] )
{

  // Stratus co-simulation initialization

#if defined(STRATUS_HLS)
  esc_initialize(argc, argv);
  esc_elaborate();
  sc_start();

#else

  // Normal SystemC simulation
  dsp_unit_top *dsp_unit_top_inst = new dsp_unit_top("dsp_unit_top_inst");

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


  open_results_files(run_name, output_dir);
  sc_start();
  close_results_files();
  cout << "SIMULATION STOPPED AT TIME = " << sc_time_stamp() << endl;
#endif

  return 0;  
}

/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Stratus co-simulation entry and exit point functions
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

#if defined(STRATUS_HLS)

extern void esc_elaborate()
{

  for (int i=1; i < esc_argc(); ++i)
    {
      if (!strcmp(esc_argv(i), "-run"))
	{
	  ++i;
	  if (i < esc_argc()) run_name = (char *) esc_argv(i);

	}
      else if (!strcmp(esc_argv(i), "-output"))
	{
	  ++i;
	  if (i < esc_argc()) output_dir = (char *) esc_argv(i);

	}
    }
  
  open_results_files(run_name, output_dir);
  stratus_dsp_unit_top_inst = new dsp_unit_top("dsp_unit_top_inst");
}

extern void esc_cleanup()
{
  delete stratus_dsp_unit_top_inst;
  close_results_files();
}

#endif

