-------------------------------------------------------------------------------
-- i2s_unit.vhd:  VHDL RTL model for the i2s_unit.
-------------------------------------------------------------------------------

-- Standard VHDL libraries

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-------------------------------------------------------------------------------
--
-- Entity declaration
--
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.audioport_vhdl_pkg.all;

entity i2s_unit is
  
  port (
    clk   : in std_logic;
    rst_n : in std_logic;
    play_in : in std_logic;
    tick_in : in std_logic;
    audio_in_0 : in std_logic_vector(23 downto 0);
    audio_in_1 : in std_logic_vector(23 downto 0);    
    cfg_in : in std_logic;
    cfg_reg_in : in std_logic_vector(31 downto 0);
    req_out : out std_logic;
    ws_out : out std_logic;
    sck_out : out std_logic;
    sdo_out : out std_logic
  );
  
end i2s_unit;

-------------------------------------------------------------------------------
--
-- Architecture declaration
--
-------------------------------------------------------------------------------

architecture RTL of i2s_unit is

  -- SCK clock divider counter
  signal sck_ctr_r : unsigned(2 downto 0);

  -- SCK clock divider modulus setting register
  signal sck_mod_r : unsigned(3 downto 0);
  
  -- WS  divider counter
  signal ws_ctr_r : unsigned(5 downto 0);

  -- Play mode register
  signal state_r : control_fsm_t;

  -- Glitch-free output waveform generator flip-flops
  signal sck_r : std_logic;
  signal ws_r : std_logic;

  -- Output shift-register control signals
  signal out_srg_shift : std_logic;
  signal out_srg_load : std_logic;

  -- Audio input FIFO signals
  type fifo_t is array (FIFO_SIZE-1 downto 0) of std_logic_vector(47 downto 0);
  signal fifo_r : fifo_t;
  signal head_r : natural range 0 to FIFO_SIZE-1;
  signal tail_r : natural range 0 to FIFO_SIZE-1;
  signal looped_r : std_logic;
  signal empty : std_logic;
  signal full : std_logic;  
  signal fifo_val : std_logic_vector(47 downto 0);
  
  -- Audio output shift-register
  signal out_srg_r : std_logic_vector(47 downto 0);
    
begin


 state_reg: process (clk, rst_n)
  begin
    if rst_n = '0' then
      state_r <= STOP;
    elsif rising_edge(clk) then

      case state_r is

        when STOP =>
          if play_in = '1' then
            state_r <= FILL;
          end if;

        when FILL =>        
          if (play_in = '1') then
            if (full = '0') then
              state_r <= REQ;
            else 
              state_r <= PLAY;
            end if;
          else
            state_r <= STOP;       
          end if;

        when REQ =>
          if (play_in = '1') then
            state_r <= LOAD;
          else
            state_r <= STOP;
          end if;

        when LOAD =>
          if (play_in = '1') then
            if (tick_in = '1') then
              state_r <= FILL;
            end if;
          else
            state_r <= STOP;
          end if;

        when PLAY =>
          if (play_in = '0' and out_srg_load = '1') then
            state_r <= STOP;
          end if;
      end case;

    end if;

  end process state_reg;

    -----------------------------------------------------------------------------
  -- FIFO registers process
  -----------------------------------------------------------------------------
  
  fifo_regs: process (clk, rst_n)
  begin
    if rst_n = '0' then
      fifo_r <= (others => (others => '0'));
      head_r <= 0;
      tail_r <= 0;
      looped_r <= '0';
    elsif rising_edge(clk) then

      if (state_r = STOP) then
        fifo_r <= (others => (others => '0'));
        head_r <= 0;
        tail_r <= 0;
        looped_r <= '0';
      else
        if tick_in = '1' and full = '0' then
          fifo_r(head_r) <= audio_in_0 & audio_in_1;
          if head_r = FIFO_SIZE-1 then
            head_r <= 0;
            looped_r <= '1';
          else
            head_r <= head_r + 1;
          end if; 
        end if;

        if out_srg_load = '1' and empty = '0' then
          if tail_r = FIFO_SIZE-1 then
            tail_r <= 0;
            looped_r <= '0';
          else
            tail_r <= tail_r + 1;
          end if; 
        end if;        
      end if;
    end if;

  end process fifo_regs;

  fifo_val <= fifo_r(tail_r);
  
  -----------------------------------------------------------------------------
  -- FIFO logic process
  -----------------------------------------------------------------------------
  
  fifo_logic: process (fifo_r, head_r, tail_r, looped_r)
  begin
    if (head_r = tail_r) then
      if looped_r = '1' then
        empty <= '0';
        full <= '1';
      else
        empty <= '1';
        full <= '0';
      end if;
    else
        empty <= '0';
        full <= '0';
    end if;
  end process fifo_logic;
  
  -----------------------------------------------------------------------------
  -- SCK clock divider counter process
  -----------------------------------------------------------------------------
  
  sck_ctr: process (clk, rst_n)
  begin  
      
  end process sck_ctr;

  -----------------------------------------------------------------------------
  -- SCK clock divider counter modulus register process
  -----------------------------------------------------------------------------
  
  sck_mod: process (clk, rst_n)
  begin  

  end process sck_mod;
  
  -----------------------------------------------------------------------------
  -- WS divider counter process
  -----------------------------------------------------------------------------

  ws_ctr: process (clk, rst_n)
  begin 

  end process ws_ctr;

  -----------------------------------------------------------------------------
  -- Glitch-free output waveform generator process
  -----------------------------------------------------------------------------
  
  sck_reg: process (clk, rst_n)
  begin  

  end process sck_reg;

  -----------------------------------------------------------------------------
  -- Glitch-free output waveform generator process
  -----------------------------------------------------------------------------
  
  ws_reg: process (clk, rst_n)
  begin  

  end process ws_reg;
  
  -----------------------------------------------------------------------------
  -- Shift-register control logic process
  -----------------------------------------------------------------------------

  out_srg_control: process (sck_ctr_r, sck_mod_r, ws_ctr_r)
  begin  

  end process out_srg_control;

  -----------------------------------------------------------------------------
  -- req_out control logic process
  -----------------------------------------------------------------------------

  req_control: process (state_r, out_srg_load, play_in)
  begin  

  end process req_control;
  
  -----------------------------------------------------------------------------
  -- Audio output shift-register process
  -----------------------------------------------------------------------------
  
  out_srg: process (clk, rst_n)
  begin  

  end process out_srg;

  -----------------------------------------------------------------------------
  -- Output assignments
  -----------------------------------------------------------------------------
  
  sck_out <= sck_r;
  ws_out <= ws_r;
  sdo_out <= out_srg_r(47);
  
end RTL;

