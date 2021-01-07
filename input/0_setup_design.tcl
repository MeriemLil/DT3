####################################################################
#
# Sub-project selection
#
####################################################################

source "input/0_setup_audioport.tcl"
#source "input/0_setup_tlm_audioport.tcl"
#source "input/0_setup_control_unit.tcl"
#source "input/0_setup_i2s_unit.tcl"
#source "input/0_setup_cdc_unit.tcl"
#source "input/0_setup_dsp_unit.tcl"

####################################################################
#
# Settings common to all subprojects
#
####################################################################

# Set this variable to 0 if you don't want the tools to open
# all generated reports in a text editor.

set SHOW_REPORTS 0

# Define Verilog compiler macro that is used in source code to 
# to detect RTL simulation

set VLOG_RTL_OPTIONS         "-suppress 13314 +define+RTL_SIM"
set XCELIUM_VLOG_RTL_OPTIONS "-DEFINE RTL_SIM"
set VCS_VLOG_RTL_OPTIONS     "+define+RTL_SIM"

# Set this to 0 when you have seen enough of the schematics 

set VSIM_SCHEMATIC 0

# Disable some commong warnings

set VSIM_GATELEVEL_OPTIONS  "+nowarn3448 -debugdb"
set VSIM_POSTLAYOUT_OPTIONS "+nowarn3448 +nowarn3438 +nowarnTSCALE"

# Assertion module bindings for the whole project are here:

set SVA_BIND_FILE "input/sva_bindings.svh"

# XML testplan file location
if { [file exists input/${DESIGN_NAME}_testplan.xml ] == 1} {
    set VSIM_TESTPLAN input/${DESIGN_NAME}_testplan.xml
}

# Testplan generation parameters
if { [info exists XML2UCDB_OPTIONS] == 0 || $XML2UCDB_OPTIONS == "" } {
    set XML2UCDB_OPTIONS "-GDESIGN_NAME=${DESIGN_NAME} -GSIM_PREFIX=/${DESIGN_NAME}_tb/DUT_INSTANCE -GFORMAL_PREFIX=/${DESIGN_NAME}"
}

# Disable SDC file if it does not exists to fall back to TCL variable

if { [info exists SDC_FILE ] } {
    if { [file exists $SDC_FILE ] == 0} {
	unset SDC_FILE
    }
}

# Filters for selecting assertions to report in Questa Formal
if { [info exists QFORMAL_BB_PROPERTIES] == 0 || $QFORMAL_BB_PROPERTIES == "" } {
    set QFORMAL_BB_PROPERTIES "CHECKER_MODULE.af_*"
}
if { [info exists QFORMAL_WB_PROPERTIES] == 0 || $QFORMAL_WB_PROPERTIES == "" } {
    set QFORMAL_WB_PROPERTIES "CHECKER_MODULE.ar_*"
}

# Make Jasper FV to run longer
set JASPER_TRACE_LENGTH 3000

# Some Design Compiler settings

set DC_SUPPRESS_MESSAGES { "UID-401" "TEST-130" "TIM-104" "TIM-134" "TIM-179" "VER-26" "VO-4" }
set DC_WRITE_PARASITICS 0


###################################################################
#
# Select backannotation delay types (MIN, TYP, MAX)
# These depends on where the synthesis and  P&R tools put
# the delays in the SDF file. Synopsys Design Compiler
# backannotate delays as "TYP", Cadence tools as "MAX"
#
###################################################################

set GATELEVEL_SDF TYP
set POSTLAYOUT_SDF MAX

