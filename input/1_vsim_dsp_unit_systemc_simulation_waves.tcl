onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clk.m_cur_val
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/rst_n
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/cfg_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clr_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/level_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/cfg_reg_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/level_reg_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp_regs_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/tick_in
add wave -noupdate -childformat {{/sc_main/dsp_unit_top_inst/dsp_unit_inst/abuf_in(0) -radix decimal} {/sc_main/dsp_unit_top_inst/dsp_unit_inst/abuf_in(1) -radix decimal}} -expand -subitemconfig {/sc_main/dsp_unit_top_inst/dsp_unit_inst/abuf_in(0) {-format Analog-Step -height 48 -max 8388610.0 -min -8388610.0 -radix decimal} /sc_main/dsp_unit_top_inst/dsp_unit_inst/abuf_in(1) {-format Analog-Step -height 48 -max 8388610.0 -min -8388610.0 -radix decimal}} /sc_main/dsp_unit_top_inst/dsp_unit_inst/abuf_in
add wave -noupdate -childformat {{/sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp_out(0) -radix decimal} {/sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp_out(1) -radix decimal}} -expand -subitemconfig {/sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp_out(0) {-format Analog-Step -height 48 -max 8388610.0 -min -8388610.0 -radix decimal} /sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp_out(1) {-format Analog-Step -height 48 -max 8388610.0 -min -8388610.0 -radix decimal}} /sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp_out
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/valid_out
add wave -noupdate -divider {Latency Check:}
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clk.m_cur_val
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/tick_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/valid_out
TreeUpdate [SetDefaultTree]
quietly wave cursor active 1
configure wave -namecolwidth 217
configure wave -valuecolwidth 225
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits us
update
wave zoom full

