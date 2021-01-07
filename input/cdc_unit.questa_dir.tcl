#
# Directive file for Questa CDC scripts
#

# Make qcdc recognize handshake synchronizers
cdc scheme on -handshake

# Make qcdc flag multibit two-dff synchronizers as violations
cdc report scheme bus_two_dff -severity violation

# Enable reconvergence analysis
#cdc preference reconvergence -depth 4
#cdc preference protocol -promote_reconvergence
#cdc reconvergence on

# Metastability window setting example:
# cdcfx fx window -start 25 -stop 10 -percent -rx_clock mclk -tx_clock clk


