with Ada.Strings.Fixed;       use Ada.Strings.Fixed;
with Ada.Characters.Handling; use Ada.Characters.Handling;
with Elists;                  use Elists;
--  with Treepr;                 use Treepr;
with Sinfo;                   use Sinfo;
with Einfo;                   use Einfo;
with Atree;                   use Atree;
with Sem_Util;                use Sem_Util;
--  with Namet;                   use Namet;
with Tree_Walk;               use Tree_Walk;
with Ada.Text_IO;             use Ada.Text_IO;
package body ASVAT_Modelling is

   Lower_Case_Models     : constant String := To_Lower (Model_List);

   -----------------
   -- Find_Model  --
   -----------------

   function Find_Model (S : String) return Model_Index is
      Lower_S   : constant String := To_Lower (S);
      Start_Pos : Positive := Lower_S'First;
      Sep_Pos   : Natural  := Index (Lower_Case_Models,
                                     "#", From => Start_Pos);
   begin
      while Sep_Pos /= 0 loop
         exit when  Lower_Case_Models (Start_Pos .. Sep_Pos - 1) = Lower_S;
         Start_Pos := Sep_Pos + 1;
         Sep_Pos   := Index (Lower_Case_Models, "#", From => Start_Pos);
      end loop;
      return Model_Index (if Sep_Pos = 0 then 0 else Start_Pos);
   end Find_Model;

   Non_Det_In_Type_Index : constant Model_Index :=
     Find_Model ("Non_Det_In_Type");
   pragma Assert (Non_Det_In_Type_Index /= 0);

   --------------
   -- Is_Model --
   --------------

   function Is_Model (S : String) return Boolean is (Find_Model (S) /= 0);

   ----------------
   -- Make_Model --
   ----------------

   procedure Make_Model (ASVAT_Model : String; Outputs : Elist_Id) is
      ASVAT_Model_Index : constant Model_Index := Find_Model (ASVAT_Model);

      type Model_Section is (Declarations, Statements);

      procedure Make_Model_Section (ASVAT_Model_Index : Model_Index;
                                    Section : Model_Section;
                                    Outputs : Elist_Id);

      procedure Make_Model_Section (ASVAT_Model_Index : Model_Index;
                                    Section : Model_Section;
                                    Outputs : Elist_Id) is
         Iter      : Elmt_Id  := First_Elmt (Outputs);
         Type_List : constant Elist_Id := New_Elmt_List;
      begin
         while Present (Iter) loop
            if Nkind (Node (Iter)) in
              N_Identifier | N_Expanded_Name | N_Defining_Identifier
            then
               declare
                  Curr_Entity : constant Node_Id :=
                    (if Nkind (Node (Iter)) = N_Defining_Identifier then
                        Node (Iter)
                     else
                        Entity (Node (Iter)));
                  Obj_Type    : constant Node_Id := Etype (Curr_Entity);
                  Type_Name   : constant String := Unique_Name (Obj_Type);
                  Obj_Name : constant String := Unique_Name (Curr_Entity);
               begin
                  if Ekind (Curr_Entity) /= E_Abstract_State then
                     if Section = Declarations then
                        if not Contains (Type_List, Obj_Type) then
                           Append_Elmt (Obj_Type, Type_List);
                           Put_Line ("Declare " & Type_Name &
                                       "_non_det : " & Type_Name);
                        end if;
                     else
                        Put_Line ("Assign " & Obj_Name & " := " &
                                    Type_Name & "_non_det");
                        if ASVAT_Model_Index = Non_Det_In_Type_Index and then
                          Is_Scalar_Type (Obj_Type)
                        then
                           Put_Line ("pragma Assume (" & Obj_Name &
                                       " in " & Type_Name & "'Range)");
                        end if;
                     end if;
                  elsif Section = Declarations then
                     --  Report unhandled node whilst generating declarations,
                     --  not again when generating statements.
                     Report_Unhandled_Node_Empty
                       (Curr_Entity, "Make_Model",
                        "Abstract_State as a global output is unsupported");
                  end if;
               end;
            elsif Section = Declarations then
               --  Report unhandled node whilst generating declarations,
               --  not again when generating statements.
               Report_Unhandled_Node_Empty
                 (Node (Iter), "Make_Model",
                  "Unsupported Global output");
            end if;

            Next_Elmt (Iter);
         end loop;
      end Make_Model_Section;

   begin
      Make_Model_Section (ASVAT_Model_Index, Declarations, Outputs);
      Make_Model_Section (ASVAT_Model_Index, Statements, Outputs);
   end Make_Model;

end ASVAT_Modelling;
