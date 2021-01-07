#
# Directive file for Questa CDC scripts
#

# Make qcdc recognize handshake synchronizers
cdc scheme on -handshake

# Make qcdc flag multibit two-dff synchronizers as violations
cdc report scheme bus_two_dff -severity violation

# Enable reconvergence analysis
cdc preference reconvergence -depth 1
cdc preference protocol -promote_reconvergence

# Metastability window tuning example:
#cdcfx fx window -start 25 -stop 25 -percent -rx_clock mclk -tx_clock clk

# Waived:
# To waive (disable) a check, select the the Violation in the CDC Checks tab,
# and execute Right button > Create directive > cdc report crossing - Waived...
# Use default settings. When you have handled (waived) all violations you think
# are false (cannot happen), activate the Directives window, and execute 
# File > Export > Directive File. Select a text file, and copy the 
# cdc report crossing ... -severity waived directives from that file
# to this file.

