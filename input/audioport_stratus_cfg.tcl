# Design parameters


# Micro-architecture directive TCL code to be passed to 'define_hls_config'

proc control_unit_constraints { } {
    define_protocol  -name "RESET_REGION"  [ find -region "RESET_REGION"]
    define_protocol  -name "PROCESSING_REGION"  [ find -region "PROCESSING_REGION"]
}

proc dsp_unit_constraints { } {
    define_protocol  -name "RESET_REGION"  [ find -region "RESET_REGION"]
    define_protocol  -name "INPUT_REGION"  [ find -region "INPUT_REGION"]
    define_protocol  -name "OUTPUT_REGION"  [ find -region "OUTPUT_REGION"]
    assume_stable    -name "stable_dsp_regs" [find -region "PROCESSING_REGION"] "dsp_proc/dsp_regs_r"
    constrain_latency -name "PROCESSING_REGION"  -min_lat 0 -max_lat 263 [find -region "PROCESSING_REGION"]
}

proc i2s_unit_constraints { } {
    define_protocol  -name "RESET_REGION"  [ find -region "RESET_REGION"]
    define_protocol  -name "PROCESSING_REGION"  [ find -region "PROCESSING_REGION"]
}

# Define HLS modules Stratus must synthesize

define_hls_module audioport           [list $LAUNCH_DIR/input/audioport.cpp]
define_hls_module control_unit        [list $LAUNCH_DIR/input/control_unit.cpp]
define_hls_module dsp_unit            [list $LAUNCH_DIR/input/dsp_unit.cpp]
define_hls_module cdc_unit            [list $LAUNCH_DIR/input/cdc_unit.cpp]
define_hls_module cdc_pulse_sync      [list $LAUNCH_DIR/input/cdc_pulse_sync.cpp]
define_hls_module cdc_2ff_sync        [list $LAUNCH_DIR/input/cdc_2ff_sync.cpp]
define_hls_module cdc_handshake_audio [list $LAUNCH_DIR/input/cdc_handshake.cpp] -template "cdc_handshake<48>"
define_hls_module cdc_handshake_cfg   [list $LAUNCH_DIR/input/cdc_handshake.cpp] -template "cdc_handshake<32>"
define_hls_module i2s_unit            [list $LAUNCH_DIR/input/i2s_unit.cpp]

# Define HLS configurations

define_hls_config audioport           BASIC_CFG  "--flatten_array=all --unroll_loops=on"
define_hls_config control_unit        BASIC_CFG  "--flatten_array=all --unroll_loops=on" -uarch_tcl "control_unit_constraints"
define_hls_config dsp_unit            BASIC_CFG  "--flatten_array=all --unroll_loops=on" -uarch_tcl "dsp_unit_constraints"
define_hls_config cdc_unit            BASIC_CFG  "--flatten_array=all --unroll_loops=on"
define_hls_config cdc_handshake_audio BASIC_CFG  "--flatten_array=all --unroll_loops=on"
define_hls_config cdc_handshake_cfg   BASIC_CFG  "--flatten_array=all --unroll_loops=on"
define_hls_config cdc_pulse_sync      BASIC_CFG  "--flatten_array=all --unroll_loops=on"
define_hls_config cdc_2ff_sync        BASIC_CFG  "--flatten_array=all --unroll_loops=on"
define_hls_config i2s_unit            BASIC_CFG  "--flatten_array=all --unroll_loops=on" -uarch_tcl "i2s_unit_constraints"

# Define logic synthesis config

define_logic_synthesis_config BASIC_CFG_LOGICSYN { audioport BASIC_CFG } { control_unit BASIC_CFG } { dsp_unit BASIC_CFG } \
    { cdc_unit BASIC_CFG } { cdc_handshake_audio BASIC_CFG } {cdc_handshake_cfg BASIC_CFG } \
    { cdc_pulse_sync BASIC_CFG } { cdc_2ff_sync BASIC_CFG } { i2s_unit BASIC_CFG } \
    -options {BDW_LS_NOGATES 1}

# Define I/O configurations (PIN interfaces only)

define_io_config audioport           PIN
define_io_config control_unit        PIN
define_io_config dsp_unit            PIN
define_io_config cdc_unit            PIN
define_io_config cdc_handshake_audio PIN
define_io_config cdc_handshake_cfg   PIN
define_io_config cdc_pulse_sync      PIN
define_io_config cdc_2ff_sync        PIN
define_io_config i2s_unit            PIN

# Define behavioral simulation configuration (for simulation from Stratus)

define_sim_config B -io_config PIN -argv "-run stratus_BEH -output ${LAUNCH_DIR}/output" { audioport BEH }

# Define RTL simulation configuration (for simulation from Stratus)

define_sim_config BASIC_CFG_RTL_V -argv "-run stratus_BASIC -output ${LAUNCH_DIR}/output" \
    -verilog_simulator ${STRATUS_VERILOG_SIMULATOR} { audioport RTL_V BASIC_CFG } { control_unit RTL_V BASIC_CFG } { dsp_unit RTL_V BASIC_CFG } \
    { cdc_unit RTL_V BASIC_CFG } { cdc_handshake_audio RTL_V BASIC_CFG } {cdc_handshake_cfg RTL_V BASIC_CFG } \
    { cdc_pulse_sync RTL_V BASIC_CFG } { cdc_2ff_sync RTL_V BASIC_CFG } { i2s_unit RTL_V BASIC_CFG } \








