#
# control_unit.sdc: Timing Constraints File
#


# 1. Define clock period and clock edge times in ns

create_clock -name clk -period 5.0 clk
set_ideal_network clk

# 2. Define reset input timing wrt clock in ns

set_input_delay  -clock clk 0.0 rst_n

# 3. Define input external delays (arrival times) wrt clock in ns

set_input_delay -clock clk 0.5 psel_in
set_input_delay -clock clk 0.5 penable_in
set_input_delay -clock clk 0.5 pwrite_in
set_input_delay -clock clk 0.5 paddr_in
set_input_delay -clock clk 0.5 pwdata_in
set_input_delay -clock clk 0.5 req_in

# 4. Define output external delays (setup times) wrt clock in ns

set_output_delay -clock clk 0.5 prdata_out
set_output_delay -clock clk 0.5 pready_out
set_output_delay -clock clk 0.5 pslverr_out
set_output_delay -clock clk 0.5 irq_out
set_output_delay -clock clk 0.5 abuf_out
set_output_delay -clock clk 0.5 cfg_out
set_output_delay -clock clk 0.5 cfg_reg_out
set_output_delay -clock clk 0.5 level_out
set_output_delay -clock clk 0.5 level_reg_out
set_output_delay -clock clk 0.5 dsp_regs_out
set_output_delay -clock clk 0.5 clr_out   
set_output_delay -clock clk 0.5 tick_out
set_output_delay -clock clk 0.5 play_out

#set_multicycle_path 2 -from {paddr_in} -to {prdata_out}
#set_multicycle_path 2 -from {psel_in} -to {prdata_out}
#set_multicycle_path 2 -from {penable_in} -to {prdata_out}
#set_multicycle_path 2 -from {pwrite_in} -to {prdata_out}
