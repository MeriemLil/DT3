// ---------------------------------------------------------------------------         
// f_psel_1
// ---------------------------------------------------------------------------
   
property f_psel_1;
   @(posedge clk) disable iff (rst_n == '0)
     (paddr_in >= AUDIOPORT_START_APB_ADDRESS && paddr_in <= AUDIOPORT_END_APB_ADDRESS) |-> psel_in;
endproperty

mf_psel_1: assume property(f_psel_1)
  else $error("psel_in == '1 while paddr_in not in AUDIOPORT range.");


// ---------------------------------------------------------------------------         
// f_psel_0
// ---------------------------------------------------------------------------
   
property f_psel_0;
   @(posedge clk) disable iff (rst_n == '0)
     !(paddr_in >= AUDIOPORT_START_APB_ADDRESS && paddr_in <= AUDIOPORT_END_APB_ADDRESS) |-> !psel_in;
endproperty

mf_psel_0: assume property(f_psel_0)
  else $error("psel_in == '0 while paddr_in not outside AUDIOPORT range.");

// ---------------------------------------------------------------------------         
// f_psel_before_penable
// ---------------------------------------------------------------------------

property f_psel_before_penable;
   @(posedge clk) disable iff (rst_n == '0)
     $rose(psel_in) |=> $rose(penable_in);
endproperty

mf_psel_before_penable: assume property(f_psel_before_penable);

// ---------------------------------------------------------------------------         
// f_penable_fall
// ---------------------------------------------------------------------------

property f_penable_fall;
   @(posedge clk) disable iff (rst_n == '0)
     (penable_in && pready_out) |=> !penable_in;
endproperty

mf_penable_fall: assume property(f_penable_fall);

// ---------------------------------------------------------------------------         
// f_penable_hold
// ---------------------------------------------------------------------------

property f_penable_hold;
   @(posedge clk) disable iff (rst_n == '0)
     (penable_in && !pready_out) |=> penable_in;
endproperty

mf_penable_hold: assume property(f_penable_hold);

// ---------------------------------------------------------------------------         
// f_apb_access
// ---------------------------------------------------------------------------

sequence s_apb_setup;
   psel_in && !penable_in;
endsequence

sequence s_apb_access;
   ($stable(paddr_in) && $stable(pwrite_in) && psel_in && penable_in && !pready_out) [* 0:32] ##1 
   ($stable(paddr_in) && $stable(pwrite_in) && psel_in && penable_in && pready_out) ##1 
   !penable_in;
endsequence

property f_apb_access;
   @(posedge clk) disable iff (rst_n == '0)
     s_apb_setup |=> s_apb_access;
endproperty

mf_apb_access: assume property(f_apb_access);



// ---------------------------------------------------------------------------      
// f_paddr_align
// ---------------------------------------------------------------------------      

property f_paddr_align;
   @(posedge clk) disable iff (rst_n == '0)
     psel_in |-> paddr_in[1:0] == 2'b00;
endproperty

mf_paddr_align: assume property(f_paddr_align)
  else $error("paddr_in not properly aligned, paddr_in[1:0] != 2'b00");

/*

property f_psel_to_penable;
   @(posedge clk) disable iff (rst_n == '0)
     $rose(psel_in) |=> $rose(penable_in);
endproperty

mf_psel_to_penable: assume property(f_psel_to_penable);

// 
property f_penable_down;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(penable_in && pready_out) |=> !penable_in;
endproperty

mf_penable_down: assume property(f_penable_down);

property f_psel_ok;
      @(posedge clk) disable iff (rst_n == '0)
	(psel_in |-> (paddr_in >= AUDIOPORT_START_APB_ADDRESS) && (paddr_in <= AUDIOPORT_END_APB_ADDRESS))
	or
        (!psel_in |-> !((paddr_in >= AUDIOPORT_START_APB_ADDRESS) && (paddr_in <= AUDIOPORT_END_APB_ADDRESS)));
endproperty

mf_psel_ok: assume property(f_psel_ok);
*/
