#
# cdc_unit.sdc: Timing Constraints File
#

# 1. Define clock period and clock edge times in ns

create_clock -name clk -period 17.5 clk
set_ideal_network clk
create_clock -name mclk -period 54.25 mclk
set_ideal_network mclk
set_clock_groups -asynchronous -name cdc_unit_clk_domains -group clk -group mclk

# 2. Define reset input timing wrt clock in ns

set_input_delay  -clock clk 5.0 rst_n
set_input_delay  -clock mclk 5.0 mrst_n

# 3. Define input external delays (arrival times) wrt clock in ns

set_input_delay  -clock clk 0.0 dsp_in
set_input_delay  -clock clk 0.0 tick_in
set_input_delay  -clock clk 0.0 cfg_in
set_input_delay  -clock clk 0.0 cfg_reg_in

# 4. Define output external delays (setup times) wrt clock in ns

set_output_delay  -clock mclk 0.0 dsp_out
set_output_delay  -clock mclk 0.0 tick_out
set_output_delay  -clock mclk 0.0 cfg_out 
set_output_delay  -clock mclk 0.0 cfg_reg_out


