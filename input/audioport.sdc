#
# audioport.sdc: Timing Constraints File
#

##############################################
#
# clk clock domain
#
##############################################

# 1. Define clock period and clock edge times in ns

create_clock -name clk -period 17.5 clk

#set_ideal_network clk
#set_propagated_clock clk

set_clock_latency  0.600 clk

set_clock_uncertainty 0.06 clk

# 2. Define reset input timing w.r.t. clock in ns

set_input_delay  -clock clk 2.5 rst_n

# 3. Define input external delays (arrival times) wrt clock in ns

set_input_delay -clock clk 0.0 psel_in
set_input_delay -clock clk 0.0 penable_in
set_input_delay -clock clk 0.0 pwrite_in
set_input_delay -clock clk 0.0 paddr_in
set_input_delay -clock clk 0.0 pwdata_in

# 4. Define output external delays (setup times) wrt clock in ns

set_output_delay -clock clk 0.0 prdata_out
set_output_delay -clock clk 0.0 pready_out
set_output_delay -clock clk 0.0 pslverr_out

set_output_delay -clock clk 0.0 irq_out

##############################################
#
# mclk clock domain
#
##############################################

# 1. Define clock period and clock edge times in ns

create_clock -name mclk -period 54.25 mclk
#set_ideal_network mclk

# 2. Define reset input timing wrt clock in ns

set_input_delay  -clock clk 0.0 mrst_n

# 3. Define input external delays (arrival times) wrt clock in ns

# 4. Define output external delays (setup times) wrt clock in ns

set_output_delay -clock mclk 0.0 ws_out
set_output_delay -clock mclk 0.0 sck_out
set_output_delay -clock mclk 0.0 sdo_out

set_clock_groups -asynchronous -name audioport_clk_domains -group clk -group mclk

##############################################
#
# Input drives and output loads
#
##############################################

set REFLIB NangateOpenCellLibrary
set BUFFER "BUF_X4"
set BUF_IN_PIN "A"
set BUF_OUT_PIN "Z"

set_driving_cell -library $REFLIB -lib_cell $BUFFER -pin $BUF_OUT_PIN [all_inputs]
remove_driving_cell [get_ports clk]

set_load [expr 2 * [load_of $REFLIB/$BUFFER/$BUF_IN_PIN]] [all_outputs]
