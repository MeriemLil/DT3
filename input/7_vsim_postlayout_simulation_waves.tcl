add wave -noupdate -divider {Post-layout:}
add wave -ports -noupdate /${DESIGN_NAME}_tb/DUT_INSTANCE/*
add wave -noupdate -divider {Reference:}
add wave -ports -noupdate /${DESIGN_NAME}_tb/REF_MODEL/REF_INSTANCE/*
configure wave -signalnamewidth 1
configure wave -datasetprefix 0




