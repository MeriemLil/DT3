###################################################################
#
# cdc_unit environment setup
#
###################################################################

set DESIGN_NAME "cdc_unit"

set DESIGN_FILES { "input/audioport_pkg.sv" \
		       "input/apb_pkg.sv" \
		       "input/audioport_util_pkg.sv" \
		       "input/cdc_unit.sv" \
		       "input/cdc_unit_svamod.sv"}
set TESTBENCH_FILES { "input/cdc_unit_test.sv" \
			   "input/cdc_unit_tb.sv" }

set RTL_LANGUAGE "SystemVerilog"

###################################################################
#
# Timing Constraints
#
###################################################################

set SDC_FILE input/${DESIGN_NAME}.sdc

set CLOCK_NAMES           {"clk" "mclk"}
set CLOCK_PERIODS         { 17.5    54.25}
set CLOCK_UNCERTAINTIES   { 0.0      0.0}
set CLOCK_LATENCIES       { 0.0      0.0}
set INPUT_DELAYS          {   0        0}
set OUTPUT_DELAYS         {   0        0}
set OUTPUT_LOAD           0.01
set RESET_NAMES           { "rst_n" "mrst_n" }
set RESET_LEVELS          { 0       0 }
set RESET_STYLES          {  "async"  "async" }
set CLOCK_DOMAIN_PORTS { { play_in tick_in dsp_in cfg_in cfg_reg_in req_out rst_n } \
			  { play_out tick_out dsp_out cfg_out cfg_reg_out req_in mrst_n} }

###################################################################
#
# Settings for simulation scripts
#
###################################################################

set RTL_SIMULATION_TIME "-all"
set GATELEVEL_SIMULATION_TIME "-all"

#set VSIM_DISABLE_TIMINGCHECKS { "*ff1*" \
#                                "*ff2*"  }
                              

###################################################################
#
# Settings for static verification scripts
#
###################################################################

set QUESTA_INIT_FILE "input/rst_mrst.questa_init"

set QUESTA_DIRECTIVES "input/cdc_unit.questa_dir.tcl"

set QFORMAL_COVERAGE 0

set QCDC_RUN_CDCFX 0

###################################################################
#
# Synthesis settings
#
###################################################################

# For gate-level simulation:
set DC_WRITE_PARASITICS 1




