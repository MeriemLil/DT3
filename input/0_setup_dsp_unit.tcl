###################################################################
#
# Settings for 'dsp_unit' top-level
#
###################################################################

set DESIGN_NAME "dsp_unit"

set DESIGN_FILES {     "input/audioport_pkg.sv" \
		       "input/apb_pkg.sv" \
		       "input/audioport_util_pkg.sv" \
			"results/dsp_unit_hls_rtl.v"
			"input/dsp_unit.sv"  \
                        "input/dsp_unit_svamod.sv" \
		    }

set TESTBENCH_FILES {  "input/dsp_unit_test.sv" \
			   "input/dsp_unit_tb.sv" }

set RTL_LANGUAGE "SystemVerilog"

set SYSTEMC_SOURCE_FILES "input/dsp_unit.cpp"
set SYSTEMC_HEADER_FILES "input/dsp_unit.h input/dsp_unit_tb.h input/dsp_unit_top.h "
set SYSTEMC_TESTBENCH_FILES "input/dsp_unit_tb.cpp input/dsp_unit_top.cpp input/dsp_unit_sc_main.cpp "
set SYSTEMC_MODULES {  "dsp_unit"  }

###################################################################
#
# Timing Constraints
#
###################################################################

set SDC_FILE input/dsp_unit.sdc

set CLOCK_NAMES           {"clk"}
set CLOCK_PERIODS         {  20 }
set CLOCK_UNCERTAINTIES   {   0 }
set CLOCK_LATENCIES       {   0 }
set INPUT_DELAYS          {   0 }
set OUTPUT_DELAYS         {   0 }
set OUTPUT_LOAD 0
set RESET_NAMES { "rst_n" }
set RESET_LEVELS { 0 }

###################################################################
#
# High-Level Synthesis Settings
#
###################################################################

#set STRATUS_EXPORTED_CONFIG "OPTIMIZED_CFG"

set STRATUS_MODULE_CONFIG_FILE "${LAUNCH_DIR}/input/dsp_unit_stratus_cfg.tcl"

set CATAPULT_DIRECTIVE_FILE "input/dsp_unit_catapult_directives.tcl"

###################################################################
#
# Settings for simulation scripts
#
###################################################################

set SYSTEMC_SIMULATION_TIME "-all"
set RTL_SIMULATION_TIME "-all"
set GATELEVEL_SIMULATION_TIME "-all"

###################################################################
#
# Settings for static verification scripts
#
###################################################################

set QUESTA_INIT_FILE "input/rst.questa_init"

# Questa Autocheck disabled modules
set QAUTOCHECK_DISABLE_MODULES { "dsp_unit_rtl" }

