onerror {resume}
#view -new wave -title ${DESIGN_NAME}
add wave -noupdate /${DESIGN_NAME}_tb/DUT_INSTANCE/*
configure wave -signalnamewidth 1
configure wave -datasetprefix 0
log -r /*



