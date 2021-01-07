###################################################################
#
# Design Specifications
#
###################################################################

set DESIGN_NAME "i2s_unit"

set DESIGN_FILES {     "input/audioport_pkg.sv"  \
		       "input/audioport_vhdl_pkg.vhd"  \
		       "input/apb_pkg.sv" \
		       "input/audioport_util_pkg.sv" \
		       "input/i2s_unit.vhd" \
		       "input/i2s_unit_svamod.sv" }

set TESTBENCH_FILES {     "input/i2s_if.sv"  \
			  "input/i2s_unit_test.sv"  \
			  "input/i2s_unit_tb.sv" }

#set RTL_LANGUAGE "SystemVerilog"
set RTL_LANGUAGE "VHDL"

###################################################################
#
# Timing Constraints
#
###################################################################

set SDC_FILE input/${DESIGN_NAME}.sdc

set CLOCK_NAME "clk"
set CLOCK_NAMES           {"clk"}
set CLOCK_PERIODS         {  20 }
set CLOCK_UNCERTAINTIES   {   0 }
set CLOCK_LATENCIES       {   0 }
set INPUT_DELAYS          {   0 }
set OUTPUT_DELAYS         {   0 }
set OUTPUT_LOAD               0
set RESET_NAMES           { "rst_n" }
set RESET_LEVELS          { 0 }
set RESET_STYLES          { "async" }

###################################################################
#
# Settings for simulation scripts
#
###################################################################

set RTL_SIMULATION_TIME       "5ms"
set GATELEVEL_SIMULATION_TIME "5ms"

###################################################################
#
# Settings for static verification scripts
#
###################################################################

# Questa static verification tool init file
set QUESTA_INIT_FILE "input/rst.questa_init"

# Make Japser recognize VHDL
set JASPER_ELABORATE_OPTIONS "-vhdl"

