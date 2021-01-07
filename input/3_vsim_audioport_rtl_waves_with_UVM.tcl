onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate  -group Clocks /audioport_tb/DUT_INSTANCE/clk
add wave -noupdate  -group Clocks /audioport_tb/DUT_INSTANCE/rst_n
add wave -noupdate  -group Clocks /audioport_tb/DUT_INSTANCE/mclk
add wave -noupdate  -group Clocks /audioport_tb/DUT_INSTANCE/mrst_n
add wave -noupdate -divider {CPU Bus}
##

if { $UVM_TESTBENCH == 1 } {
    if { $UVM_TESTNAME == "apb_test" } {
	add wave -noupdate -group APB sim:/uvm_root/uvm_test_top/m_env/m_agent/m_sequencer/seq
    }
    if { $UVM_TESTNAME == "control_unit_uvm_test" } {
	add wave -noupdate -group APB sim:/uvm_root/uvm_test_top/m_env/m_control_unit_agent/m_sequencer/seq
    }
    if { $UVM_TESTNAME == "audioport_uvm_test" } {
	add wave -noupdate -group APB sim:/uvm_root/uvm_test_top/m_env/m_control_unit_agent/m_sequencer/main_seq
    }
}
##

add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/psel_in
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/penable_in
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/pwrite_in
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/paddr_in
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/pwdata_in
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/prdata_out
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/pready_out
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/pslverr_out
add wave -noupdate -group APB /audioport_tb/DUT_INSTANCE/irq_out
add wave -noupdate -divider I2S
add wave -noupdate -group I2S /audioport_tb/DUT_INSTANCE/ws_out
add wave -noupdate -group I2S /audioport_tb/DUT_INSTANCE/sck_out
add wave -noupdate -group I2S /audioport_tb/DUT_INSTANCE/sdo_out

add wave -noupdate -divider {INTERNAL (clk)}
add wave -noupdate  -group AUDIO -childformat {{{/audioport_tb/DUT_INSTANCE/abuf[1]} -radix decimal} {{/audioport_tb/DUT_INSTANCE/abuf[0]} -radix decimal}}  -subitemconfig {{/audioport_tb/DUT_INSTANCE/abuf[1]} {-format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal} {/audioport_tb/DUT_INSTANCE/abuf[0]} {-format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal}} /audioport_tb/DUT_INSTANCE/abuf
add wave -noupdate  -group AUDIO -childformat {{{/audioport_tb/DUT_INSTANCE/dsp[1]} -radix decimal} {{/audioport_tb/DUT_INSTANCE/dsp[0]} -radix decimal}}  -subitemconfig {{/audioport_tb/DUT_INSTANCE/dsp[1]} {-format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal} {/audioport_tb/DUT_INSTANCE/dsp[0]} {-format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal}} /audioport_tb/DUT_INSTANCE/dsp

add wave -noupdate  -group AUDIO /audioport_tb/DUT_INSTANCE/play
add wave -noupdate  -group AUDIO /audioport_tb/DUT_INSTANCE/tick
add wave -noupdate  -group AUDIO /audioport_tb/DUT_INSTANCE/dsp_tick
add wave -noupdate  -group AUDIO /audioport_tb/DUT_INSTANCE/req

add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/cfg
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/cfg_reg
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/level_reg
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/dsp_regs
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/level
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/clr

add wave -noupdate -divider {INTERNAL (mclk)}

add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mplay
add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mtick
add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mreq
add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mcfg
add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mcfg_reg
add wave -noupdate  -group {mclk DOMAIN} -childformat {{{/audioport_tb/DUT_INSTANCE/mdsp[1]} -radix decimal} {{/audioport_tb/DUT_INSTANCE/mdsp[0]} -radix decimal}}  -subitemconfig {{/audioport_tb/DUT_INSTANCE/mdsp[1]} {-format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal} {/audioport_tb/DUT_INSTANCE/mdsp[0]} {-format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal}} /audioport_tb/DUT_INSTANCE/mdsp

if { $UVM_TESTBENCH == 1 && $UVM_TESTNAME == "audioport_uvm_test"} {

    add wave -noupdate -divider {DUT-vs-REF}
    
    add wave -noupdate -group DUT -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal {/audioport_tb/i2s/monitor/audio_out[1]}
    add wave -noupdate -group DUT -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal {/audioport_tb/i2s/monitor/audio_out[0]}
    add wave -noupdate -group REF -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/dsp_outputs[1]
    add wave -noupdate -group REF -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/dsp_outputs[0]
}

TreeUpdate [SetDefaultTree]
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
wave zoom full
