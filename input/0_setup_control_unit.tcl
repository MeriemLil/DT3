###################################################################
#
# control_unit environment setup
#
###################################################################

set DESIGN_NAME "control_unit"

set DESIGN_FILES [list \
		      "input/apb_pkg.sv" \
		      "input/audioport_pkg.sv" \
		      "input/audioport_util_pkg.sv" \
		      "input/apb_if.sv" \
		      "input/irq_out_if.sv" \
		      "input/control_unit.sv" \
		      "input/control_unit_svamod.sv" \
		     ]

set TESTBENCH_FILES [list \
			 "input/${DESIGN_NAME}_test.sv" \
		         "input/${DESIGN_NAME}_tb.sv" \
			]

set RTL_LANGUAGE "SystemVerilog"

###################################################################
#
# Timing Constraints
#
###################################################################

set SDC_FILE input/${DESIGN_NAME}.sdc

set CLOCK_NAMES           {"clk"}
set CLOCK_PERIODS         { 5.0 }
set CLOCK_UNCERTAINTIES   {   0 }
set CLOCK_LATENCIES       {   0 }
set INPUT_DELAYS          { 1.0 }
set OUTPUT_DELAYS         { 1.0 }
set OUTPUT_LOAD             0
set RESET_NAMES           { "rst_n" }
set RESET_STYLES          { "async" }
set RESET_LEVELS          { 0 }

###################################################################
#
# Settings for simulation scripts
#
###################################################################

# Simulation run times (set to "-all" to run all)
set RTL_SIMULATION_TIME        "-all"
set GATELEVEL_SIMULATION_TIME "-all"

###################################################################
#
# Settings for static verification scripts
#
###################################################################

# Static verification tool init file
set QUESTA_INIT_FILE "input/rst.questa_init"
set JASPER_INIT_FILE "input/rst.jasper_init"

# Questa static verification directives file for user-created directives
set QUESTA_DIRECTIVES "input/control_unit.questa_dir.tcl"

# Questa PropertyCheck
set QFORMAL_TIMEOUT        2h
set QFORMAL_COVERAGE       0

# Example: How to make Questa prove only a selected set of assertions:

#set QFORMAL_TARGETS { control_unit.CHECKER_MODULE.af_prdata_unselect \
#		      control_unit.CHECKER_MODULE.af_cfg_reg_write \
#		      }

