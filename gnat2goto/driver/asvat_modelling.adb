with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Elists;            use Elists;
with Treepr;            use Treepr;
with Sinfo;             use Sinfo;
with Einfo;             use Einfo;
with Atree;             use Atree;
with Sem_Util;          use Sem_Util;
with Ada.Text_IO;       use Ada.Text_IO;
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

   procedure Make_Model (Name : String; Outputs : Elist_Id) is
      Iter : Elmt_Id := First_Elmt (Outputs);
   begin
      pragma Assert (Is_Model (Name));
      while Present (Iter) loop
         Print_Node_Briefly (Node (Iter));
         if Nkind (Node (Iter)) in N_Identifier | N_Expanded_Name
         then
            Print_Node_Briefly (Entity (Node (Iter)));
            Print_Node_Briefly (Etype (Entity (Node (Iter))));
            Put_Line (Unique_Name (Etype (Entity (Node (Iter)))));
            Put_Line (Entity_Kind'Image
                      (Ekind (Entity (Node (Iter)))));
            Put_Line (Unique_Name (Entity (Node (Iter))));
         else
            Print_Node_Briefly (Etype (Node (Iter)));
            Put_Line (Entity_Kind'Image (Ekind (Node (Iter))));
            Put_Line (Unique_Name (Etype (Node (Iter))));
            Put_Line (Unique_Name (Node (Iter)));
         end if;

         Next_Elmt (Iter);
      end loop;
   end Make_Model;

end ASVAT_Modelling;
