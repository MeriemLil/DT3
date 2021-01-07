-------------------------------------------------------------------------------
--
-- Minimal version of audioport_pkg in VHDL format.
--
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package audioport_vhdl_pkg is

  constant RATE_48000 : std_logic_vector(1 downto 0) := "00";
  constant RATE_96000 : std_logic_vector(1 downto 0) := "01";
  constant RATE_192000 : std_logic_vector(1 downto 0) := "10";  
  
  constant MCLK_DIV_48000 : natural := 8;
  constant MCLK_DIV_96000 : natural :=  4;
  constant MCLK_DIV_192000 : natural := 2;

  constant FIFO_SIZE : positive := 4;

  type control_fsm_t is (STOP, FILL, REQ, LOAD, PLAY);
  
end audioport_vhdl_pkg;

