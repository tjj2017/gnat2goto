with Ada.Strings.Fixed;       use Ada.Strings.Fixed;
with Ada.Characters.Handling; use Ada.Characters.Handling;
with Elists;                  use Elists;
with Nlists;                  use Nlists;
with Stringt;                 use Stringt;
with Sinput;                  use Sinput;
--  with Treepr;                 use Treepr;
with Namet;                   use Namet;
with Tree_Walk;               use Tree_Walk;
with Sem_Prag;                use Sem_Prag;
with Symbol_Table_Info;       use Symbol_Table_Info;
with Ada.Text_IO;             use Ada.Text_IO;
package body ASVAT_Modelling is

   Lower_Case_Models     : constant String := To_Lower (Model_List);
--   Lower_Non_Det         : constant String := To_Lower (Non_Det);
   Lower_Non_Det_In_Type : constant String := To_Lower (Non_Det_In_Type);
   Lower_From_Unit : constant String := To_Lower (From_Unit);

   function Replace_Dots (S : String) return String;
   function Replace_Local_With_Import
     (Is_Type : Boolean; E : Entity_Id; Print_Message : Boolean) return String;

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

   ---------------------------
   -- Get_Import_Convention --
   ---------------------------

   function Get_Import_Convention (N : Node_Id) return String is
      --  The gnat front end insists thet the parameters for
      --  pragma Import are given in the specified order even
      --  if named association is used:
      --  1. Convention,
      --  2. Enity,
      --  3. Optional External_Name,
      --  4. Optional Link_Name.
      --  The first 2 parameters are mandatory and
      --  for ASVAT models the External_Name is required.
      --
      --  The Convention parameter will always be present as
      --  the first parameter.
      Conv_Assoc : constant Node_Id :=
        First (Pragma_Argument_Associations (N));
      Conv_Name  : constant Name_Id := Chars (Conv_Assoc);
      Convention : constant String  := Get_Name_String
        (Chars (Expression (Conv_Assoc)));
   begin
      --  Double check the named parameter if named association is used.
      pragma Assert (Conv_Name = No_Name or else
                     Get_Name_String (Conv_Name) = "convention");
      return Convention;
   end Get_Import_Convention;

   ------------------------------
   -- Get_Import_External_Name --
   ------------------------------

   function Get_Import_External_Name (N : Node_Id) return String is
      --  The gnat front end insists thet the parameters for
      --  pragma Import are given in the specified order even
      --  if named association is used:
      --  1. Convention,
      --  2. Enity,
      --  3. Optional External_Name,
      --  4. Optional Link_Name.
      --  The first 2 parameters are mandatory and
      --  for ASVAT models the External_Name is required.
      --
      --  The External_Name parameter, if present, will be
      --  the third parameter.
      External_Assoc : constant Node_Id := Next
        (Next
           (First (Pragma_Argument_Associations (N))));
   begin
      if Present (External_Assoc) then
         declare
            External_Name : constant Name_Id := Chars (External_Assoc);
            External_Name_Id : constant String_Id :=
              Strval (Expression (External_Assoc));
            External_Name_Id_Length : constant Natural :=
              Natural (String_Length (External_Name_Id));
         begin
            --  Double check the named parameter if named association is used.
            pragma Assert (External_Name = No_Name or else
                             Get_Name_String
                               (External_Name) = "external_name");
            String_To_Name_Buffer (External_Name_Id);
            return Name_Buffer (1 .. External_Name_Id_Length);
         end;
      else
         return "";
      end if;
   end Get_Import_External_Name;

   --------------------------
   -- Get_Import_Link_Name --
   --------------------------

   function Get_Import_Link_Name (N : Node_Id) return String is
      --  The gnat front end insists thet the parameters for
      --  pragma Import are given in the specified order even
      --  if named association is used:
      --  1. Convention,
      --  2. Enity,
      --  3. Optional External_Name,
      --  4. Optional Link_Name.
      --  The first 2 parameters are mandatory and
      --  for ASVAT models the External_Name is required
      --  and for imported non-visible objects, Link_Name is required.
      --  The Link_Name parameter, if present, will be
      --  the Fourth parameter.
      External_Assoc : constant Node_Id := Next
        (Next
           (First (Pragma_Argument_Associations (N))));
      Link_Assoc     : constant Node_Id :=
        (if Present (External_Assoc) then Next (External_Assoc)
         else External_Assoc);
   begin
      if Present (Link_Assoc) then
         declare
            Link_Name    : constant Name_Id := Chars (Link_Assoc);
            Link_Name_Id : constant String_Id :=
              Strval (Expression (Link_Assoc));
            Link_Name_Id_Length : constant Natural :=
              Natural (String_Length (Link_Name_Id));
         begin
            --  Double check the named parameter if named association is used.
            pragma Assert (Link_Name = No_Name or else
                             Get_Name_String
                               (Link_Name) = "link_name");
            String_To_Name_Buffer (Link_Name_Id);
            return Name_Buffer (1 .. Link_Name_Id_Length);
         end;
      else
         return "";
      end if;
   end Get_Import_Link_Name;

   --------------
   -- Is_Model --
   --------------

   function Is_Model (E : Entity_Id) return Boolean is
      Obj_Import_Pragma : constant Node_Id := Import_Pragma (E);
      Is_Ada : constant Boolean :=
        (if Present (Obj_Import_Pragma) then
              Get_Import_Convention (Obj_Import_Pragma) = "ada"
         else
            False);
      External_Name : constant String :=
        (if Is_Ada then
            Get_Import_External_Name (Obj_Import_Pragma)
         else
            "");
   begin
      return Is_Ada and then Find_Model (External_Name) /= 0;
   end Is_Model;

   -------------------
   -- Is_Model_Sort --
   -------------------

   function Is_Model_Sort (E : Entity_Id; Model : String) return Boolean is
      Obj_Import_Pragma : constant Node_Id := Get_Pragma (E, Pragma_Import);
      Is_Ada : constant Boolean :=
        (if Present (Obj_Import_Pragma) then
              Get_Import_Convention (Obj_Import_Pragma) = "ada"
         else
            False);
      External_Name : constant String :=
        (if Is_Ada then
            Get_Import_External_Name (Obj_Import_Pragma)
         else
            "");
   begin
      return Is_Ada and then To_Lower (Model) = To_Lower (External_Name);
   end Is_Model_Sort;

   function Is_Model_String (S : String) return Boolean is
     (Find_Model (S) /= 0);

   ----------------
   -- Make_Model --
   ----------------

   procedure Make_Model (E : Entity_Id) is
      Subprog_Import_Pragma : constant Node_Id := Import_Pragma (E);
      Model : constant String :=
        (if Present (Subprog_Import_Pragma) then
              To_Lower (Get_Import_External_Name (Subprog_Import_Pragma))
         else
            "");

      type Model_Section is (Declarations, Statements);

      procedure Make_Model_Section (Model : String;
                                    Section : Model_Section;
                                    Outputs : Elist_Id);

      procedure Make_Model_Section (Model : String;
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

                  Obj_Name : constant String :=
                    (if Is_Imported (Curr_Entity) and then
                     Is_Model_Sort (Curr_Entity, From_Unit) then
                          Replace_Local_Object_With_Import (Curr_Entity, False)
                     else
                        Unique_Name (Curr_Entity));

                  Obj_Type    : constant Node_Id := Etype (Curr_Entity);

                  Replacement : constant String :=
                    (if Is_Imported (Curr_Entity) and then Is_Model_Sort
                     (Curr_Entity, From_Unit)
                     then
                        Replace_Local_Type_With_Import
                       (Curr_Entity, False)
                     else
                        "");

                  Type_Name   : constant String :=
                    (if Is_Imported (Curr_Entity) and then Replacement /= ""
                     and then Global_Symbol_Table.Contains
                       (Intern
                            (Replacement))
                     then
                        Replace_Local_Type_With_Import (Curr_Entity, True)
                     else
                       Unique_Name (Etype (Curr_Entity)));

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
                        if Model =  Lower_Non_Det_In_Type and then
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

      --  Get lists of all the inputs and outputs of the model
      --  subprogram including all those listed in a pragma Global.
      --  Presently the list of inputs is not used.

      Model_Inputs  : Elist_Id := No_Elist;
      Model_Outputs : Elist_Id := No_Elist;
      Global_Seen   : Boolean;
   begin
      Collect_Subprogram_Inputs_Outputs
        (Subp_Id      => E,
         Synthesize   => False,
         Subp_Inputs  => Model_Inputs,
         Subp_Outputs => Model_Outputs,
         Global_Seen  => Global_Seen);
      if not Global_Seen then
         Put_Line
           (Standard_Error,
            "Global pragma expected for imported ASVAT model.");
         Put_Line
           (Standard_Error,
            "Specify 'Global => null' if the model has no " &
              "global variables");
      end if;

      Put_Line (Build_Location_String (Sloc (Subprog_Import_Pragma)) &
                  " ASVAT modelling:");
      Put_Line ("Adding a " & Model &
                  " body for imported subprogram " &
                  Unique_Name (E));

      Make_Model_Section (Model, Declarations, Model_Outputs);
      Make_Model_Section (Model, Statements, Model_Outputs);
   end Make_Model;

   --------------------------------------
   -- Replace_Local_Object_With_Import --
   --------------------------------------

   function Replace_Local_Object_With_Import
     (E : Entity_Id; Print_Message : Boolean) return String is
     (Replace_Local_With_Import (Is_Type       => False,
                                 E             => E,
                                 Print_Message => Print_Message));

   -------------------------------------
   -- Replace_Local_Type_With_Import --
   -------------------------------------

   function Replace_Local_Type_With_Import
     (E : Entity_Id; Print_Message : Boolean) return String is
     (Replace_Local_With_Import (Is_Type       => True,
                                 E             => E,
                                 Print_Message => Print_Message));

   -------------------------------
   -- Replace_Local_With_Import --
   -------------------------------

   function Replace_Local_With_Import
     (Is_Type : Boolean; E : Entity_Id; Print_Message : Boolean) return String
   is
      Obj_Import_Pragma : constant Node_Id := Get_Pragma (E, Pragma_Import);
      Is_Replace : constant Boolean :=
        (if Present (Obj_Import_Pragma) then
              To_Lower (Get_Import_External_Name (Obj_Import_Pragma)) =
             Lower_From_Unit
         else
            False);
      Import_Unit : constant String :=
        Replace_Dots (Get_Import_Link_Name (Obj_Import_Pragma));

      Local_Name : constant String :=
        (if Is_Type then Get_Name_String (Chars (Etype (E)))
         else Get_Name_String (Chars (E)));

      Replacement_Name : constant String :=
        (if Import_Unit /= "" then Import_Unit & "__" else "") &
        Local_Name;

   begin
      if Is_Replace then

         if Print_Message then
            Put_Line (Build_Location_String (Sloc (Obj_Import_Pragma)) &
                        " ASVAT modelling: ");
            Put_Line ("Replacing local name '" &
                        Local_Name & "' by '" & Replacement_Name & "'");
         end if;

         return Replacement_Name;
      else
         Report_Unhandled_Node_Empty
           (Obj_Import_Pragma,
            "ASVAT_Modelling.Rename_Local_To_External",
            "Unsupported pragma Import of object");
         return Unique_Name (E);
      end if;
   end Replace_Local_With_Import;

   function Replace_Dots (S : String) return String is
      function Replace_Dots_Rec (So_Far : String;
                                 Pos : Natural) return String;
      function Replace_Dots_Rec (So_Far : String;
                                 Pos : Natural) return String is
      begin
         if Pos in S'Range then
            if S (Pos) = '.' then
               return Replace_Dots_Rec (So_Far & "__", Pos + 1);
            else
               return Replace_Dots_Rec (So_Far & To_Lower (S (Pos)), Pos + 1);
            end if;
         else
            return So_Far; --  (if So_Far /= "" then So_Far & "__" else "");
         end if;
      end Replace_Dots_Rec;

   begin
      return Replace_Dots_Rec ("", S'First);
   end Replace_Dots;

end ASVAT_Modelling;
