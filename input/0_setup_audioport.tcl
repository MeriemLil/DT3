###################################################################
#
# audioport Environment Settings
#
###################################################################

set DESIGN_NAME "audioport"

set DESIGN_SUBMODULES { "control_unit" "dsp_unit" "cdc_unit" "i2s_unit" }

set DESIGN_FILES {     "input/apb_pkg.sv" \
		       "input/audioport_pkg.sv" \
		       "input/audioport_util_pkg.sv" \
		       "input/audioport_vhdl_pkg.vhd" \
		       "input/apb_if.sv" \
		       "input/irq_out_if.sv" \
		       "input/i2s_if.sv" \
		       "input/control_unit.sv" \
		       "results/dsp_unit_hls_rtl.v" \
		       "input/dsp_unit.sv" \
		       "input/cdc_unit.sv" \
		       "input/i2s_unit.vhd" \
		       "input/audioport.sv" \
		       "input/control_unit_svamod.sv" \
		       "input/dsp_unit_svamod.sv" \
		       "input/cdc_unit_svamod.sv" \
		       "input/i2s_unit_svamod.sv"  \
		       "input/audioport_svamod.sv"  \
		   }

set TESTBENCH_FILES { \
			  "input/apb_uvm_pkg.sv" \
			  "input/irq_agent_uvm_pkg.sv" \
			  "input/control_unit_uvm_pkg.sv" \
			  "input/i2s_agent_uvm_pkg.sv" \
			  "input/audioport_uvm_pkg.sv" \
			  "input/audioport_test.sv" \
			  "input/audioport_tb.sv" \
		      }

set RTL_LANGUAGE "SystemVerilog"

#####################################################################################
# SystemC code settings
#
#    1 = use SystemC code only for dsp_unit
#    0 = use SystemC code for all modules
#
#####################################################################################

if { 0 } {
    set SYSTEMC_SOURCE_FILES "input/dsp_unit.cpp"
    set SYSTEMC_HEADER_FILES "input/dsp_unit.h"
} else {
    set SYSTEMC_SOURCE_FILES  { \
				    "input/control_unit.cpp" \
				    "input/dsp_unit.cpp" \
				    "input/cdc_handshake.cpp" \
				    "input/cdc_pulse_sync.cpp" \
				    "input/cdc_2ff_sync.cpp" \
				    "input/cdc_unit.cpp" \
				    "input/i2s_unit.cpp" \
				    "input/audioport.cpp" \
				}
    
    set SYSTEMC_HEADER_FILES    { \
				      "input/control_unit.h" \
				      "input/dsp_unit.h" \
				      "input/cdc_handshake.h" \
				      "input/cdc_pulse_sync.h" \
				      "input/cdc_2ff_sync.h" \
				      "input/cdc_unit.h" \
				      "input/i2s_unit.h" \
				      "input/audioport.h" \
				  }
    
    set SYSTEMC_TESTBENCH_FILES { \
				      "input/audioport_tb.cpp" \
				      "input/audioport_top.cpp" \
				      "input/audioport_sc_main.cpp" \
				  }
    
    set SYSTEMC_MODULES { \
			      "control_unit" \
			      "dsp_unit" \
			      "cdc_handshake" \
			      "cdc_pulse_sync" \
			      "cdc_2ff_sync" \
			      "cdc_unit" \
			      "i2s_unit" \
			      "audioport" \
			  }
}

###################################################################
#
# Timing Constraints
#
###################################################################

set SDC_FILE input/${DESIGN_NAME}.sdc

set CLOCK_NAMES           {"clk" "mclk"}
set CLOCK_PERIODS         {17.5    54.25}
set CLOCK_UNCERTAINTIES   { 0.0     0.0}
set CLOCK_LATENCIES       { 0.0     0.0}
set INPUT_DELAYS          {   0       0}
set OUTPUT_DELAYS         {   0       0}
set OUTPUT_LOAD           0.01
set RESET_NAMES           { "rst_n" "mrst_n" }
set RESET_LEVELS          {  0        0 }
set RESET_STYLES          {  "async"  "async" }
set CLOCK_DOMAIN_PORTS    { { psel_in penable_in pwrite_in paddr_in pwdata_in prdata_out pready_out pslverr_out \
			      irq_out test_mode_sel rst_n } \
			  {  ws_out sck_out sdo_out mrst_n} }

###################################################################
#
# Settings for simulation scripts
#
###################################################################

set UVM_TESTBENCH 0
set UVM_TESTNAME "apb_test"
#set UVM_TESTNAME "control_unit_uvm_test"
#set UVM_TESTNAME "audioport_uvm_test"

set VSIM_RTL_WAVES "input/3_vsim_audioport_rtl_waves_with_UVM.tcl"
set VSIM_MIXEDLANG_WAVES "input/3_vsim_audioport_rtl_waves_with_UVM.tcl"

# Simulation run times (set to "-all" to run all)
set RTL_SIMULATION_TIME        "-all"
set GATELEVEL_SIMULATION_TIME  "-all"
set POSTLAYOUT_SIMULATION_TIME "-all"
set MIXEDLANG_SIMULATION_TIME  "-all"

# Enable generation of SAIF activity file
set RTL_POWER_ESTIMATION 1

# User RTL model as reference for postayout simulation
set POSTLAYOUT_VS_RTL_SIMULATION 1

# Disable checks for synchronizers
# set VSIM_DISABLE_TIMINGCHECKS {  "*sff1*" }

# Coverage Testplan Generation Settings
set XML2UCDB_OPTIONS ""

###################################################################
#
# Settings for static verification scripts
#
###################################################################

# Initialization file for Questa Formal
set QUESTA_INIT_FILE "input/rst_mrst.questa_init"

# Questa Formal coverage enable and max runtime
set QFORMAL_COVERAGE 0
set QFORMAL_TIMEOUT  48h

# Directives file for Questa (CDC)
set QUESTA_DIRECTIVES "input/audioport.questa_dir.tcl"

# Enable metastability injection in Questa CDC
set QCDC_RUN_CDCFX 1

# Enable reconvergence analysis in Questa CDC
set QCDC_RECONVERGENCE 0

# Questa Autocheck disabled modules
set QAUTOCHECK_DISABLE_MODULES { "dsp_unit_rtl" }

###################################################################
#
# RTL Synthesis Settings
#
###################################################################

# For gate-level simulation:
set DC_WRITE_PARASITICS 1

# Enable register retiming in synthesis
# set SYNTHESIS_RETIME 1

# Prevent 'compile_ultra' from breaking your module hierarchy
set SYNTHESIS_DONT_UNGROUP { "dsp_unit_1" "control_unit_1" "i2s_unit_1" "cdc_unit_1"}

set DC_MAX_CORES 8

###################################################################
#
# Formality Logic Equivalence Check Settings
#
###################################################################

set FORMALITY_TIMEOUT_LIMIT "02:00:00"

###################################################################
#
# Design-fo-Test and ATPG Configuration
#
###################################################################

# Scan chain settings for 5 chains, modify if necessary
set INSERT_SCAN_CHAINS 5
set SCAN_ENABLE_NAME "test_mode_sel"
set SCAN_IN_NAMES  { "paddr_in[0]" "paddr_in[1]" "paddr_in[2]" "paddr_in[3]" "paddr_in[4]" }
set SCAN_OUT_NAMES { "prdata_out[0]" "prdata_out[1]" "prdata_out[2]" "prdata_out[3]" "prdata_out[4]" }

set POSTLAYOUT_ATPG 1

# Tetramax run-time limit
set TETRAMAX_ABORT_LIMIT 1

# Continue with previous patters?
set TETRAMAX_CONTINUE_ATPG 0

###################################################################
#
# Power Settings
#
###################################################################

# Clock-gating setup (initially disabled)
#set GATED_CLOCKS { "clk" "mclk" }
#set UNGATED_CLOCKS {  }
#set CLOCK_GATE_MAX_FANOUT 128 
#set GATE_CLOCK_INTEGRATED 1

# VCD dump start time and length for power simulation
set VCD_SNAPSHOT_START_TIME 172us
set VCD_SNAPSHOT_LENGTH 15us

# Select power waveforms to display
set WV_WAVEFORMS { "audioport" "dsp_unit_1" "control_unit_1" "i2s_unit_1" "cdc_unit_1" }

###################################################################
#
# Place & route settings
#
###################################################################

# Innovus routability estimate
set INNOVUS_FLOORPLAN_ANALYSIS 0

# Innovus fast trial-route
set INNOVUS_TRIAL_ROUTE 0

# Cell density: make it smaller to improve routability
set INNOVUS_STANDARD_CELL_DENSITY 0.7

# Innovus effort setting
set INNOVUS_OPTIMIZATION_EFFORT "express"

set INNOVUS_DEMO_MODE 0

set INNOVUS_CPUS 8

