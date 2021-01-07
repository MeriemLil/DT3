`include "audioport.svh"

import audioport_pkg::*;

module i2s_unit(
		input logic 	   clk,
		input logic 	   rst_n,
		input logic 	   play_in,
		input logic 	   tick_in,
		input logic [23:0] audio_in_0,
		input logic [23:0] audio_in_1, 
		input logic 	   cfg_in,
		input logic [31:0] cfg_reg_in,
		output logic 	   req_out,
		output logic 	   ws_out,
		output logic 	   sck_out,
		output logic 	   sdo_out
		);

   enum 			   logic [2:0] { STOP = 3'b000, FILL = 3'b001, REQ = 3'b010, LOAD = 3'b011, PLAY = 3'b100} state_r;
   logic [47:0] 		   fifo_r[FIFO_SIZE-1:0];
   logic [31:0] 		   head_r;
   logic [31:0] 		   tail_r;
   logic [47:0] 		   fifo_val;
   logic 			   looped_r;
   logic 			   empty;
   logic 			   full;
   logic [2:0] 			   sck_ctr_r;
   logic [3:0] 			   sck_mod_r;   
   logic [5:0] 			   ws_ctr_r;
   logic [47:0] 		   out_srg_r;
   logic 			   sck_r;
   logic 			   ws_r;
   logic 			   out_srg_load;
   logic 			   out_srg_shift;

   always_ff @(posedge clk or negedge rst_n)
     begin : state_reg
	if (rst_n == '0)
	  begin
	     state_r <= STOP;
	  end
	else
	  begin
	     case (state_r)
               STOP:
		 if (play_in)
		   state_r <= FILL;
               FILL:
		 if (play_in)
		   begin
		      if (!full)
			state_r <= REQ;
		      else 
			state_r <= PLAY;
		   end
		 else
		   state_r <= STOP;       

               REQ:
		 if (play_in)
		   state_r <= LOAD;
		 else
		   state_r <= STOP;
	       
               LOAD:
		 if (play_in)
		   begin
		      if (tick_in)
			state_r <= FILL;
		   end
		 else
		   state_r <= STOP;
	       
               PLAY:
		 if (!play_in && out_srg_load)
		   state_r <= STOP;
	     endcase;
	  end
     end // block: state_reg

   always_ff @(posedge clk or negedge rst_n)
     begin : fifo_regs
	if (rst_n == '0)
	  begin
	     for (int i = 0; i < FIFO_SIZE; ++i)
	       fifo_r[i] <= '0;
	     head_r <= '0;
	     tail_r <= '0;
	     looped_r <= '0;
	  end
	else
	  begin
	     if (state_r == STOP) 
	       begin
		  for (int i = 0; i < FIFO_SIZE; ++i)
		    fifo_r[i] <= '0;
		  head_r <= '0;
		  tail_r <= '0;
		  looped_r <= '0;
	       end
	     else 
	       begin
		  if (tick_in == '1 && full == '0) 
		    begin
		       fifo_r[head_r] <= { audio_in_0, audio_in_1 };
		       if (head_r == FIFO_SIZE-1) 
			 begin
			    head_r <= 0;
			    looped_r <= '1;
			 end
		       else
			 head_r <= head_r + 1;
		    end // if (tick_in == '1 && full == '0)
		  
		  if (out_srg_load == '1 && empty == '0)
		    begin
		       if (tail_r == FIFO_SIZE-1)
			 begin
			    tail_r <= 0;
			    looped_r <= '0;
			 end
		       else
			 tail_r <= tail_r + 1;
		    end
	       end // else: !if(state_r = STOP)
	  end // else: !if(rst_n == '0)
     end : fifo_regs
   
   assign fifo_val = fifo_r[tail_r];
  
   
   always_comb
     begin : fifo_logic
	if (head_r == tail_r)
	  begin
	     if (looped_r)
	       begin
		  empty = '0;
		   full = '1;
	       end
	      else
		begin
		   empty = '1;
		   full = '0;
		end
	  end
	else
	  begin
             empty = '0;
             full = '0;
	  end // else: !if(head_r == tail_r)
     end : fifo_logic

   always_ff @(posedge clk or negedge rst_n)
     begin : sck_ctr
	if (rst_n == '0)
	  begin
	     sck_ctr_r <= '0;
	  end
	else
	  begin
	     if (state_r == PLAY)
	       begin
		  if (sck_ctr_r < sck_mod_r-1)
		    sck_ctr_r <= sck_ctr_r + 1;
		  else
		    sck_ctr_r <= 0;
	       end
	     else
	       sck_ctr_r <= 0;	       
	  end // else: !if(rst_n == '0)
     end : sck_ctr

   always_ff @(posedge clk or negedge rst_n)
     begin : sck_mod
	if (rst_n == '0)
	  begin
	     sck_mod_r <= MCLK_DIV_48000;
	  end
	else
	  begin
	     if (cfg_in == '1 && state_r == STOP && !play_in)
	       begin
		  case (cfg_reg_in[1:0])
		    RATE_48000:
		      sck_mod_r <= MCLK_DIV_48000;
		    RATE_96000:
		      sck_mod_r <= MCLK_DIV_96000;
		    RATE_192000:
		      sck_mod_r <= MCLK_DIV_192000;
		  endcase
	       end
	  end // else: !if(rst_n == '0)
     end : sck_mod

   always_ff @(posedge clk or negedge rst_n)
     begin : ws_ctr
	if (rst_n == '0)
	  begin
	     ws_ctr_r <= 0;
	  end
	else
	  begin
	     if (state_r == PLAY)
	       begin
		  if (sck_ctr_r == sck_mod_r-1)
		    begin
		       if (ws_ctr_r != 47)
			 ws_ctr_r <= ws_ctr_r + 1;
		       else
			 ws_ctr_r <= 0;
		    end
	       end
	     else
	       ws_ctr_r <= 0;
	     
	  end // else: !if(rst_n == '0)
     end : ws_ctr

   always_ff @(posedge clk or negedge rst_n)
     begin : sck_reg
	if (rst_n == '0)
	  begin
	     sck_r <= '0;
	  end
	else
	  begin
	     if (state_r == PLAY && sck_ctr_r < sck_mod_r/2)
	       sck_r <= '1;
	     else
	       sck_r <= '0;
	  end // else: !if(rst_n == '0)
     end : sck_reg

   always_ff @(posedge clk or negedge rst_n)
     begin : ws_reg
	if (rst_n == '0)
	  begin
	     ws_r <= '0;
	  end
	else
	  begin
	     if (state_r == PLAY && sck_ctr_r == sck_mod_r/2 && (ws_ctr_r == 23 || ws_ctr_r == 47))
	       ws_r <= ~ws_r;
	  end // else: !if(rst_n == '0)
     end : ws_reg
   
   always_comb
     begin : srg_control
	if ((sck_ctr_r == sck_mod_r/2) && ws_ctr_r == 0)	  
	  out_srg_load = '1;
	else
	  out_srg_load = '0;

	if ((sck_ctr_r == sck_mod_r/2) && ws_ctr_r != 0)	  
	  out_srg_shift = '1;
	else
	  out_srg_shift = '0;
     end : srg_control

   always_comb
     begin : req_control
	if (state_r == REQ)
	  req_out = '1;
	else if (state_r == PLAY && play_in == '1 && out_srg_load == '1)
	  req_out = '1;        
	else
	  req_out = '0;                
     end : req_control
   
   always_ff @(posedge clk or negedge rst_n)
     begin : out_srg
	if (rst_n == '0)
	  begin
	     out_srg_r <= '0;
	  end
	else
	  begin
	     if (state_r == PLAY)
	       begin
		  if (out_srg_load == '1)
		    begin
		       if (empty == '0)
			 out_srg_r <= fifo_val;
		    end
		  else if (out_srg_shift == '1)
		    out_srg_r <= { out_srg_r[46:0], 1'b0 };		    
	       end
	     else
	       out_srg_r <= '0;	       
	  end // else: !if(rst_n == '0)
     end : out_srg
   
   assign sck_out = sck_r;
   assign ws_out = ws_r;
   assign sdo_out = out_srg_r[47];

   
endmodule
