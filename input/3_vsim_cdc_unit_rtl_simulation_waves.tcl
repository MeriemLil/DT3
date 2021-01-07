onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/clk
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/rst_n
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/mclk
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/mrst_n
add wave -noupdate -expand -group play /cdc_unit_tb/DUT_INSTANCE/play_in
add wave -noupdate -expand -group play /cdc_unit_tb/DUT_INSTANCE/play_out
add wave -noupdate -expand -group req /cdc_unit_tb/DUT_INSTANCE/req_in
add wave -noupdate -expand -group req /cdc_unit_tb/DUT_INSTANCE/req_out
add wave -noupdate -expand -group config /cdc_unit_tb/DUT_INSTANCE/cfg_in
add wave -noupdate -expand -group config /cdc_unit_tb/DUT_INSTANCE/cfg_reg_in
add wave -noupdate -expand -group config /cdc_unit_tb/DUT_INSTANCE/cfg_out
add wave -noupdate -expand -group config /cdc_unit_tb/DUT_INSTANCE/cfg_reg_out
add wave -noupdate -expand -group audio /cdc_unit_tb/DUT_INSTANCE/tick_in
add wave -noupdate -expand -group audio /cdc_unit_tb/DUT_INSTANCE/dsp_in
add wave -noupdate -expand -group audio /cdc_unit_tb/DUT_INSTANCE/tick_out
add wave -noupdate -expand -group audio /cdc_unit_tb/DUT_INSTANCE/dsp_out
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/tick_in_r
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/play_in_r
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/cfg_in_r
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/dsp_in_r
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/cfg_reg_in_r
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/req_in_r
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/req
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/past_req_r
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/dsp_in_hs/clk1
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {351161 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
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
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ps} {2005748 ps}
