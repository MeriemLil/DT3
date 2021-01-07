#ifndef _dsp_unit_hls_directives_h_
#define _dsp_unit_hls_directives_h_ 1


//////////////////////////////////////////////////////////////////////
//
// STRATUS HLS Directives
//
//////////////////////////////////////////////////////////////////////

#if defined(STRATUS_HLS) 

#if defined(UNCONSTRAINED_CFG)

#define hls_directive_reset_region HLS_DEFINE_PROTOCOL("reset")
#define hls_directive_input_region HLS_DEFINE_PROTOCOL("input")
#define hls_directive_processing_region HLS_CONSTRAIN_LATENCY(0, -1, "process")
#define hls_directive_output_region HLS_DEFINE_PROTOCOL("output")
#define hls_directive_unroll_loop(loop) HLS_UNROLL_LOOP(ON, loop)
#define hls_directive_flatten_array(array) HLS_FLATTEN_ARRAY( array )
#define hls_directive_map_to_reg_bank(array) HLS_MAP_TO_REG_BANK( array )
 
#elif defined (ASAP_CFG)

#define hls_directive_reset_region HLS_DEFINE_PROTOCOL("reset")
#define hls_directive_input_region HLS_DEFINE_PROTOCOL("input")
#define hls_directive_processing_region HLS_CONSTRAIN_LATENCY(0, -1, "process")
#define hls_directive_output_region HLS_DEFINE_PROTOCOL("output")
#define hls_directive_unroll_loop(loop) HLS_UNROLL_LOOP(ON, loop)
#define hls_directive_flatten_array(array) HLS_FLATTEN_ARRAY( array )
#define hls_directive_map_to_reg_bank(array) HLS_MAP_TO_REG_BANK( array )

#elif defined (LATENCY_CONSTRAINED_CFG)

#define hls_directive_reset_region HLS_DEFINE_PROTOCOL("reset")
#define hls_directive_input_region HLS_DEFINE_PROTOCOL("input")
#define hls_directive_processing_region HLS_CONSTRAIN_LATENCY(0, HLS_MAX_LATENCY, "process")
#define hls_directive_output_region HLS_DEFINE_PROTOCOL("output")
#define hls_directive_unroll_loop(loop) HLS_UNROLL_LOOP(ON, loop)
#define hls_directive_flatten_array(array) HLS_FLATTEN_ARRAY( array )
#define hls_directive_map_to_reg_bank(array) HLS_MAP_TO_REG_BANK( array )

#else

#define hls_directive_reset_region
#define hls_directive_input_region
#define hls_directive_processing_region 
#define hls_directive_output_region
#define hls_directive_unroll_loop(loop)
#define hls_directive_flatten_array(array)
#define hls_directive_map_to_reg_bank(array)
#endif

#else

//////////////////////////////////////////////////////////////////////
//
// Other tools compile these:
//
//////////////////////////////////////////////////////////////////////

#define hls_directive_reset_region
#define hls_directive_input_region
#define hls_directive_processing_region 
#define hls_directive_output_region
#define hls_directive_flatten_array(array)
#define hls_directive_map_to_reg_bank(array)
#define hls_directive_unroll_loop(loop)

#endif
#endif
