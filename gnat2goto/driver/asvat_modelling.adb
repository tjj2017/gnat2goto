with Ada.Strings.Fixed; use Ada.Strings.Fixed;
package body ASVAT_Modelling is

   --------------
   -- Is_Model --
   --------------

   function Is_Model (S : String) return Boolean is
      Start_Pos : Positive := S'First;
      Sep_Pos   : Natural  := Index (Model_List, "#", From => Start_Pos);
      Found     : Boolean  := False;
   begin
      while Sep_Pos /= 0 loop
         Found :=  Model_List (Start_Pos .. Sep_Pos - 1) = S;
         exit when Found;
         Start_Pos := Sep_Pos + 1;
         Sep_Pos   := Index (Model_List, "#", From => Start_Pos);
      end loop;
      return Found;
   end Is_Model;

end ASVAT_Modelling;
