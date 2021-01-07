onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /audioport_tb/DUT_INSTANCE/clk
add wave -noupdate /audioport_tb/DUT_INSTANCE/rst_n
add wave -noupdate /audioport_tb/DUT_INSTANCE/mclk
add wave -noupdate /audioport_tb/DUT_INSTANCE/mrst_n
add wave -noupdate /audioport_tb/DUT_INSTANCE/psel_in
add wave -noupdate /audioport_tb/DUT_INSTANCE/penable_in
add wave -noupdate /audioport_tb/DUT_INSTANCE/pwrite_in
add wave -noupdate /audioport_tb/DUT_INSTANCE/paddr_in
add wave -noupdate /audioport_tb/DUT_INSTANCE/pwdata_in
add wave -noupdate /audioport_tb/DUT_INSTANCE/prdata_out
add wave -noupdate /audioport_tb/DUT_INSTANCE/pready_out
add wave -noupdate /audioport_tb/DUT_INSTANCE/pslverr_out
add wave -noupdate /audioport_tb/DUT_INSTANCE/irq_out
add wave -noupdate /audioport_tb/DUT_INSTANCE/ws_out
add wave -noupdate /audioport_tb/DUT_INSTANCE/sck_out
add wave -noupdate /audioport_tb/DUT_INSTANCE/sdo_out
add wave -noupdate /audioport_tb/DUT_INSTANCE/test_mode_sel
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {69477104 ps} 0}
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
configure wave -timelineunits us
update
WaveRestoreZoom {0 ps} {179791896 ps}
