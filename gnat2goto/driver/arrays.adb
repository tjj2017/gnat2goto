with Stand;                 use Stand;
with Nlists;                use Nlists;
with Uintp;                 use Uintp;
--  with Namet;                 use Namet;
with Stringt;               use Stringt;
with Tree_Walk;             use Tree_Walk;
with Aggregates;            use Aggregates;
--  with Follow;                use Follow;
with Range_Check;           use Range_Check;
with ASVAT.Size_Model;
with Sem_Util;              use Sem_Util;
with Sem_Eval;              use Sem_Eval;
with Gnat2goto_Itypes;      use Gnat2goto_Itypes;
with Arrays.Low_Level;      use Arrays.Low_Level;
with Treepr;                use Treepr;
with Text_IO;               use Text_IO;
with Symbol_Table_Info;     use Symbol_Table_Info;
package body Arrays is
   function Defining_Identifier (N : Node_Id) return Entity_Id;
   function Defining_Identifier (N : Node_Id) return Entity_Id is
      NT : constant Node_Kind := Nkind (N);
   begin
      if not
        (NT = N_Component_Declaration
        or else NT = N_Defining_Program_Unit_Name
        or else NT = N_Discriminant_Specification
        or else NT = N_Entry_Body
        or else NT = N_Entry_Declaration
        or else NT = N_Entry_Index_Specification
        or else NT = N_Exception_Declaration
        or else NT = N_Exception_Renaming_Declaration
        or else NT = N_Formal_Object_Declaration
        or else NT = N_Formal_Package_Declaration
        or else NT = N_Formal_Type_Declaration
        or else NT = N_Full_Type_Declaration
        or else NT = N_Implicit_Label_Declaration
        or else NT = N_Incomplete_Type_Declaration
        or else NT = N_Iterated_Component_Association
        or else NT = N_Iterator_Specification
        or else NT = N_Loop_Parameter_Specification
        or else NT = N_Number_Declaration
        or else NT = N_Object_Declaration
        or else NT = N_Object_Renaming_Declaration
        or else NT = N_Package_Body_Stub
        or else NT = N_Parameter_Specification
        or else NT = N_Private_Extension_Declaration
        or else NT = N_Private_Type_Declaration
        or else NT = N_Protected_Body
        or else NT = N_Protected_Body_Stub
        or else NT = N_Protected_Type_Declaration
        or else NT = N_Single_Protected_Declaration
        or else NT = N_Single_Task_Declaration
        or else NT = N_Subtype_Declaration
        or else NT = N_Task_Body
        or else NT = N_Task_Body_Stub
         or else NT = N_Task_Type_Declaration)
      then
         Put_Line ("Defining_Identifier - Arrays");
         Put_Line ("Illegal node to Defining_Identifier");
         Print_Node_Briefly (N);
      end if;

      return Sinfo.Defining_Identifier (N);
   end Defining_Identifier;

   package Debug_Help is
      function Print_Node (N : Node_Id; Subtree : Boolean := False)
                           return Boolean;
      function Print_Irep_Func (I : Irep) return Boolean;
      function Print_Msg (Msg : String) return Boolean;
--        pragma Unreferenced (Print_Irep_Func);
   end Debug_Help;

   package body Debug_Help is
      function Print_Node (N : Node_Id; Subtree : Boolean := False)
                           return Boolean is
      begin
         if Subtree then
            Print_Node_Subtree (N);
         else
            Print_Node_Briefly (N);
         end if;
         return True;
      end Print_Node;

      function Print_Irep_Func (I : Irep) return Boolean is
      begin
         Print_Irep (I);
         return True;
      end Print_Irep_Func;

      function Print_Msg (Msg : String) return Boolean is
      begin
         Put_Line (Msg);
         return True;
      end Print_Msg;
   end Debug_Help;
   use Debug_Help;

   function Is_Unconstrained_Array_Result (Expr : Irep) return Boolean
     renames Arrays.Low_Level.Is_Unconstrained_Array_Result;

   procedure Array_Object_And_Friends
     (Array_Name   : String;
      Array_Node   : Node_Id;
      Array_Bounds : Static_And_Dynamic_Bounds;
      The_Array    : out Irep;
      Source_Loc   : Irep;
      Block        : Irep)
   with Pre => Is_Array_Type (Underlying_Type (Etype (Array_Node)));

   procedure Array_Assignment_Op (S            : String;
                                  Source_Expr  : Node_Id;
                                  N_Dimensions : Pos;
                                  Dest_Bounds  : Static_And_Dynamic_Bounds;
                                  Target_Array : Irep;
                                  Block        : Irep)
   with Pre => Is_Array_Type (Etype (Source_Expr)) and
               Kind (Get_Type (Target_Array)) = I_Array_Type;

   procedure Declare_Array_Friends (Array_Name  : String;
                                    Src_Array   : Node_Id;
                                    Flat_Bounds : Static_And_Dynamic_Bounds;
                                    Block       : Irep)
     with Pre => Is_Array_Type (Etype (Src_Array)) and
          Kind (Block) = I_Code_Block;
   --  An unconstrained array object declaration has to be suplemented
   --  by the declaration of the array friend variables
   --  Array_Name___first_<Dimension> and Array_Name___last_<Dimension>
   --  for each dimension of the array.

   procedure Declare_First_Last_From_Bounds (Prefix     : String;
                                             Dimension  : String;
                                             Index_Type : Irep;
                                             Bounds     : Dimension_Bounds;
                                             Block      : Irep);
   --  This is similar to Declare_First_Last_Vars but is called at a slightly
   --  lower-level with the index node replaced by the Index_Type Irep and
   --  the dimension Bounds.

   procedure Declare_First_Last_From_Object (Target_Name : String;
                                             Object_Name : String;
                                             Dimension   : Positive;
                                             Block       : Irep);

   procedure Declare_First_Last_Params (Prefix     : String;
                                        Dimension  : Positive;
                                        Index      : Node_Id;
                                        Param_List : Irep);
   --  Each dimension of an unconstrained array parameter
   --  introduces two extra friend parameters of mode in to a subprogram.
   --  The values passed in these extra parameters are the lower and upper
   --  bounds of each dimension of the unconstrained array parameter.
   --  The parameters representing the lower and upper bounds of the
   --  dimension are of the base type of the index type.
   --  Their names of the variables are <Prefix>___first_<Dimension>,
   --  and <Prefix>___last_<Dimension>.

   procedure Declare_First_Last_Vars (Prefix     : String;
                                      Dimension  : Positive;
                                      Index      : Node_Id;
                                      Block      : Irep);
   --  A declatation of an unconstrained array object has to be supplemented
   --  by declarations of friend variables to represent the upper and lower
   --  bounds of each dimension of the array object.
   --  The variables representing the lower and upper bounds of the
   --  dimension are of the base type of the index type.
   --  Their names of the variables are <Prefix>___first_<Dimension>,
   --  and <Prefix>___last_<Dimension>.

   function Do_Array_First_Last (N         : Node_Id;
                                 Dimension : Pos)
                                 return Dimension_Bounds
     with Pre => Is_Array_Type (Etype (N));

   function Get_Dimension_Index (The_Array : Entity_Id; Dim : Pos)
                                 return Node_Id;

   function Get_Underlying_Array_From_Slice (N : Node_Id) return Node_Id
     with Pre => Nkind (N) = N_Slice;

--     procedure Make_Array_Object_From_Bounds (Block          : Irep;
--                                              Array_Name     : String;
--                                              Target_Type    : Entity_Id;
--                                              Array_Length   : Irep;
--                                         Array_Bounds   : Dimension_Bounds;
--                                              Needs_Size_Var : Boolean;
--                                              Source_Loc     : Irep;
--                                              The_Array      : out Irep)
--       with Pre => (Is_Array_Type (Target_Type) and
--                   not Is_Constrained (Target_Type)) and then
--                   Number_Dimensions (Target_Type) = 1;
   --  Decalre a one-dimensional array from the given target type,
   --  its length and its bounds.
   --  Also declare the First and Last companion variables for the
   --  unconstrained array.

   procedure Make_Constrained_Array_From_Initialization
     (Block        : Irep;
      Array_Name   : String;
      Init_Expr    : Node_Id;
      The_Array    : out Irep;
      Array_Bounds : out Static_And_Dynamic_Bounds);

   function Make_Constrained_Array_Subtype (Declaration : Node_Id) return Irep;

   function Make_Unconstrained_Array_Subtype (Declaration    : Node_Id;
                                              Component_Type : Entity_Id)
                                              return Irep;
   procedure Update_Array_From_Concatenation
           (Block        : Irep;
            Concat      : Node_Id;
            Dest_Bounds : Static_And_Dynamic_Bounds;
            Dest_Array  : Irep)
     with Pre => Nkind (Concat) = N_Op_Concat and
                 Kind (Get_Type (Dest_Array)) = I_Array_Type;

   procedure Update_Array_From_Slice
           (Block       : Irep;
            Slice       : Node_Id;
            Dest_Array  : Irep;
            Dest_Bounds : Static_And_Dynamic_Bounds)
     with Pre => Nkind (Slice) = N_Slice and
     Kind (Get_Type (Dest_Array)) = I_Array_Type;

   procedure Update_Array_From_String_Literal
     (Block        : Irep;
      Str_Lit      : Node_Id;
      Dest_Array   : Irep)
     with Pre => Nkind (Str_Lit) = N_String_Literal;

--     procedure Array_Assignment_Op (Source_Node : Node_Id;
--                                    Target_Node : Node_Id;
--                                    Is_Assign   : Boolean;
--                                    Block       : Irep);
--     is
--      Location         : constant Irep := Get_Source_Location (Target_Node);
--
--        Target_Type      : constant Entity_Id := Etype (Target_Node);
--        Source_Type      : constant Entity_Id := Etype (Source_Node);
--
--        Target_Is_Slice  : constant Boolean :=
--          Nkind (Target_Node) = N_Slice;
--        Source_Is_Slice  : constant Boolean :=
--          Nkind (Source_Node) = N_Slice;
--        Has_Slices        : constant Boolean :=
--          Target_Is_Slice or Source_Is_Slice;
--        Is_Aggregate     : constant Boolean :=
--          Nkind (Source_Node) = N_Aggregate;
--        Is_Function_Call : constant Boolean :=
--          Nkind (Source_Node) = N_Function_Call;
--        Is_Concat_Op     : constant Boolean :=
--          Nkind (Source_Node) = N_Op_Concat;
--
--        Is_Unconstrained : constant Boolean :=
--       not Is_Constrained (Source_Type) and not Is_Constrained (Target_Type);
--        Has_Static_Bounds : constant Boolean :=
--          not Is_Unconstrained and then
--          All_Dimensions_Static (Source_Type) and
--          All_Dimensions_Static (Target_Type);
--
--        Dest : constant Irep :=
--          (if Is_Assign and (Is_Aggregate or Has_Slices) then
--                Declare_Temp_Array (Target_Type, Block)
--               elsif
--        procedure Simple_Array_Assignment;
--        procedure Simple_Array_Assignment is
--           Target_Ty : constant Irep := Get_Type (Target_Irep);
--        begin
--           Append_Op (Block,
--                      Make_Code_Assign
--                        (Rhs             =>
--                           Typecast_If_Necessary
--                             (Expr           => Source_Irep,
--                              New_Type       => Target_Ty,
--                              A_Symbol_Table => Global_Symbol_Table),
--                         Lhs             => Target_Irep,
--                         Source_Location => Location,
--                         I_Type          => Target_Ty,
--                         Range_Check     => False));
--        end Simple_Array_Assignment;
--
--     begin
--        if Source_Node not in
--          N_Identifier    | N_Expanded_Name |
--          N_Aggregate     | N_Slice         |
--          N_Function_Call | N_Op_Concat
--        then
--           Report_Unhandled_Node_Empty
--             (N        => Source_Node,
--              Fun_Name => "Array_Assignment_Op",
--              Message  => "Unsupported RHS of assignement operation " &
--                Node_Kind'Image (Nkind (Source_Node)));
--        elsif Is_Unconstrained then
--           Report_Unhandled_Node_Empty
--             (N        => N,
--              Fun_Name => "Array_Assignment_Op",
--         Message  => "Unconstrained assignment operations are unsupported");
--           --  As a simple recovery action - but not semantically correct
--              --  perform a simple assignment.
--              Simple_Array_Assignment;
--
--        elsif Has_Static_Bounds and No_Slices then
--           --  A simple array assignment is all that is needed.
--           Simple_Array_Assignment;
--        elsif Is_

   procedure Array_Assignment_Op (S            : String;
                                  Source_Expr  : Node_Id;
                                  N_Dimensions : Pos;
                                  Dest_Bounds  : Static_And_Dynamic_Bounds;
                                  Target_Array : Irep;
                                  Block        : Irep)
   is
      --        Source_Location    : constant Irep :=
      --  Get_Source_Location (Source_Expr);

      RHS_Node_Kind      : constant Node_Kind := Nkind (Source_Expr);
      RHS_Entity         : constant Node_Id :=
        (if RHS_Node_Kind in N_Entity then
            Source_Expr
         elsif RHS_Node_Kind in N_Has_Entity then
            Entity (Source_Expr)
         else
            Types.Empty);
      RHS_Is_Object      : constant Boolean :=
        Present (RHS_Entity) and then Is_Object (RHS_Entity);

      Source_Type        : constant Entity_Id :=
        Underlying_Type (Etype (Source_Expr));
--        Component_I_Type   : constant Irep :=
--          Make_Resolved_I_Type (Component_Type (Source_Type));
      Source_I_Type      : constant Irep :=
        (if RHS_Is_Object then
            Global_Symbol_Table (Intern (Unique_Name (RHS_Entity))).SymType
         else
            Do_Type_Reference (Source_Type));

--        Target_I_Type      : constant Irep := Get_Type (Target_Array);
   begin
      Put_Line ("Array_Assignment_Op " & S);
      Put_Line ("Array_Assignment_Op Low " &
                  Int'Image (Dest_Bounds.Low_Static));
      Put_Line ("Array_Assignment_Op High "
                & Int'Image (Dest_Bounds.High_Static));
      if RHS_Node_Kind = N_Aggregate then
         Update_Array_From_Aggregate
           (Block        => Block,
            Agg          => Source_Expr,
            N_Dimensions => N_Dimensions,
            Dest_Bounds  => Dest_Bounds,
            Dest_Array   => Target_Array);
      elsif RHS_Node_Kind = N_String_Literal then
         Update_Array_From_String_Literal
            (Block        => Block,
             Str_Lit      => Source_Expr,
             Dest_Array   => Target_Array);
      elsif RHS_Node_Kind = N_Slice then
         Update_Array_From_Slice
           (Block       => Block,
            Slice       => Source_Expr,
            Dest_Array  => Target_Array,
            Dest_Bounds => Dest_Bounds);
      elsif RHS_Node_Kind = N_Op_Concat then
         Put_Line ("Array_Assignment_Op - Update from concat");
         Update_Array_From_Concatenation
           (Block       => Block,
            Concat      => Source_Expr,
            Dest_Array  => Target_Array,
            Dest_Bounds => Dest_Bounds);
      else
         --  ***********************************************************
         --  TODO: Variable Arrays.
         --  This check and reporting should be removed
         --  when cbmc properly handles arrays with bounds specified by
         --  a variable and support for unconstrained array function
         --  results are supported.
         if RHS_Node_Kind = N_Function_Call then
            if not Is_Constrained (Source_Type) then
               Report_Unhandled_Node_Empty
                 (N        => Source_Expr,
                  Fun_Name => "Array_Assignment_Op",
                  Message  =>
                    "Functions returning an unconstrained array "
                  & "are currently unsupported");
            elsif not All_Dimensions_Static (Source_Type) then
               Report_Unhandled_Node_Empty
                 (N        => Source_Expr,
                  Fun_Name => "Array_Assignment_Op",
                  Message  =>
                    "Functions returning an array with non-static bounds "
                  & "are currently unsupported");
               --  *******************************************************
            end if;
         end if;

         declare
            Resolved_Source_Expr : constant Irep :=
              Typecast_If_Necessary
                (Expr           => Do_Expression (Source_Expr),
                 New_Type       => Source_I_Type,
                 A_Symbol_Table => Global_Symbol_Table);
            Source_Bounds : constant Static_And_Dynamic_Bounds :=
              Multi_Dimension_Flat_Bounds ("50", Source_Expr);
         begin
            Assign_Array
              (Block         => Block,
               Destination   => Target_Array,
               Dest_Bounds   => Dest_Bounds,
               Source        => Resolved_Source_Expr,
               Source_Bounds => Source_Bounds);
         end;
      end if;
   end Array_Assignment_Op;

   procedure Array_Object_And_Friends
     (Array_Name   : String;
      Array_Node   : Node_Id;
      Array_Bounds : Static_And_Dynamic_Bounds;
      The_Array    : out Irep;
      Source_Loc   : Irep;
      Block        : Irep)
   is
      Src_Array_Kind   : constant Node_Kind := Nkind (Array_Node);
      Id               : constant Symbol_Id := Intern (Array_Name);
      Src_Array_Type   : constant Entity_Id :=
        Underlying_Type (Etype (Array_Node));
      Src_Entity       : constant Entity_Id :=
        (if Src_Array_Kind in N_Entity then
            Array_Node
         elsif Src_Array_Kind in N_Has_Entity then
            Entity (Array_Node)
         else
            Types.Empty);
      Src_Is_Object     : constant Boolean :=
       (if Present (Src_Entity) then
            Is_Object (Src_Entity)
         else
            False);

      Comp_Type        : constant Entity_Id :=
        Component_Type (Src_Array_Type);
      Comp_Irep        : constant Irep :=
        Make_Resolved_I_Type (Comp_Type);

      Src_Array_I_Type : constant Irep := Do_Type_Reference (Src_Array_Type);

   begin
      Put_Line ("Array_Object_And_Friends");
      Put_Line (Array_Name);
      Print_Node_Briefly (Array_Node);
      Print_Node_Briefly (Src_Array_Type);
      Print_Irep (Array_Bounds.Low_Dynamic);
      Print_Irep (Array_Bounds.High_Dynamic);
      Put_Line ("Is an object " &
                  Boolean'Image (Src_Is_Object));

      declare
         Array_Size : constant Static_And_Dynamic_Index :=
           Get_Array_Size_From_Bounds (Array_Bounds);

         Needs_Size_Var : constant Boolean :=
           (not Is_Constrained (Src_Array_Type) or else
                (not Array_Bounds.Has_Static_Bounds and then
                 Is_Itype (Src_Array_Type)));
         --  A constrained array with non-static bounds will have had
         --  the size variable declaraed when it was declared unless it
         --  is an Itype declaration.

         Array_Size_Var  : constant Irep :=
           (if Needs_Size_Var then
               Make_Symbol_Expr
              (Source_Location => Source_Loc,
               I_Type          => Index_T,
               Range_Check     => False,
               Identifier      => Array_Name & "_$array_size")
            else
               Ireps.Empty);
         Array_Type_Irep : constant Irep :=
           (if Array_Size_Var = Ireps.Empty then
            --  Does not need a size var, which means the array subtype has
            --  static bounds or the size variable has been declared and
            --  intialised in the goto code when the array was declared.
            --  In either case the Irep array type from the Do_Type_Reference
            --  can be used.
               Src_Array_I_Type
            else
            --  A new variable has to be declared to represent the size of
            --  the goto array object.
               Make_Array_Type
              (I_Subtype => Comp_Irep,
               Size      => Array_Size_Var));

         Array_Irep : constant Irep :=
           Make_Symbol_Expr
             (Source_Location => Source_Loc,
              I_Type          => Array_Type_Irep,
              Range_Check     => False,
              Identifier      => Array_Name);
         Decl      : constant Irep := Make_Code_Decl
           (Symbol => Array_Irep,
            Source_Location => Source_Loc);

      begin
         Put_Line ("Array_Object_And_Friends");
         Put_Line ("Needs_Size_Var " & Boolean'Image (Needs_Size_Var));
         Print_Irep (Src_Array_I_Type);
         Print_Node_Briefly (Src_Array_Type);
         if not Global_Symbol_Table.Contains (Id) then
            --  If a size variable is needed to define the size of the
            --  goto array object, declare it before the array.
            Put_Line ("The symbol table does not contain the array");
            Print_Irep (Array_Size_Var);
            Print_Irep (Array_Size.Dynamic_Index);
            if Kind (Array_Size.Dynamic_Index) = I_Op_Add then
               Put_Line ("LHS");
               Print_Irep (Get_Lhs (Array_Size.Dynamic_Index));
               Put_Line ("RHS");
               Print_Irep (Get_Rhs (Array_Size.Dynamic_Index));
            end if;

            if Needs_Size_Var then
               Append_Declare_And_Init
                 (Symbol     => Array_Size_Var,
                  Value      => Array_Size.Dynamic_Index,
                  Block      => Block,
                  Source_Loc => Source_Loc);
            end if;

            Append_Op (Block, Decl);
            New_Object_Symbol_Entry
              (Object_Name       => Id,
               Object_Type       => Array_Type_Irep,
               Object_Init_Value => Ireps.Empty,
               A_Symbol_Table    => Global_Symbol_Table);

            --  The model size of the object has to be recorded.
            if Is_Constrained (Src_Array_Type) then
               if ASVAT.Size_Model.Has_Static_Size (Src_Array_Type) then
                  ASVAT.Size_Model.Set_Static_Size
                    (Id         => Id,
                     Model_Size =>
                       ASVAT.Size_Model.Static_Size (Src_Array_Type));
               else
                  ASVAT.Size_Model.Set_Computed_Size
                    (Id        => Id,
                     Size_Expr =>
                       ASVAT.Size_Model.Computed_Size (Src_Array_Type));
               end if;
            elsif Src_Is_Object then
               if ASVAT.Size_Model.Has_Static_Size (Src_Entity) then
                  ASVAT.Size_Model.Set_Static_Size
                    (Id         => Id,
                     Model_Size =>
                       ASVAT.Size_Model.Static_Size (Src_Entity));
               else
                  ASVAT.Size_Model.Set_Computed_Size
                    (Id        => Id,
                     Size_Expr =>
                       ASVAT.Size_Model.Computed_Size (Src_Entity));
               end if;

            elsif not Array_Bounds.Is_Unconstrained then
               ASVAT.Size_Model.Set_Computed_Size
                 (Id        => Id,
                  Size_Expr => Make_Op_Mul
                    (Rhs             => Array_Size.Dynamic_Index,
                     Lhs             => Typecast_If_Necessary
                       (Expr           =>
                            ASVAT.Size_Model.Computed_Size (Comp_Type),
                        New_Type       => Int32_T,
                        A_Symbol_Table => Global_Symbol_Table),
                     Source_Location => Source_Loc,
                     I_Type          => Int32_T));
            else
               Report_Unhandled_Node_Empty
                 (N        => Array_Node,
                  Fun_Name => "Array_Object_And_Friends",
                  Message  => "Unexpected unconstrained array result");
            end if;

            --  The first and last variables for each dimension have to
            --  added to the symbol table and initialised.

            Put_Line ("About to call Declare_Array_Friends");
            Declare_Array_Friends
              (Array_Name  => Array_Name,
               Src_Array   => Array_Node,
               Flat_Bounds => Array_Bounds,
               Block      => Block);
         end if;
         --  Ensure the out variables are set.
         The_Array := Array_Irep;
      end;
   end Array_Object_And_Friends;

   -----------------------------
   -- Do_Array_Assignment_Op  --
   -----------------------------

   procedure Do_Array_Assignment_Op (Block       : Irep;
                                     Destination : Irep;
                                     Dest_Type   : Entity_Id;
                                     Source_Expr : Node_Id)
   is
      Underlying : constant Entity_Id := Underlying_Type (Dest_Type);
      pragma Assert (Print_Msg ("Do_Array_Assignment_Op"));
      pragma Assert (Print_Node (Dest_Type));
      pragma Assert (Print_Node (Underlying, True));
      Array_Bounds : constant Static_And_Dynamic_Bounds :=
            Multi_Dimension_Flat_Bounds ("20", Underlying);
   begin
      if Array_Bounds.Is_Unconstrained then
         Report_Unhandled_Node_Empty
           (N        => Source_Expr,
            Fun_Name => "Do_Array_Assignment_Op",
            Message  => "Assignment expression cannot be unconstrained");
      else
         Array_Assignment_Op
           ("1",
            Source_Expr  => Source_Expr,
            N_Dimensions => Number_Dimensions (Underlying),
            Dest_Bounds  => Array_Bounds,
            Target_Array => Destination,
            Block        => Block);
      end if;
   end Do_Array_Assignment_Op;

   ----------------------------------
   -- Do_Array_Object_Declaration  --
   ----------------------------------

   procedure Do_Array_Object_Declaration (Block       : Irep;
                                          Dec_Node    : Node_Id;
                                          Target_Type : Entity_Id;
                                          Array_Name  : String;
                                          Init_Expr   : Node_Id)
   is
      Source_Loc     : constant Irep := Get_Source_Location (Dec_Node);
      Target_Def     : constant Entity_Id := Defining_Identifier (Dec_Node);
      Array_Id       : constant Symbol_Id := Intern (Array_Name);
      Underlying     : constant Entity_Id := Underlying_Type (Target_Type);

      pragma Assert (Print_Msg ("Is_Constrained (Underlying) " &
                       Boolean'Image (Is_Constrained (Underlying))));
      pragma Assert (Print_Msg ("Is_Constr (Underlying) " &
                       Boolean'Image
                       (Is_Constr_Subt_For_U_Nominal (Underlying))));
      Array_Bounds : Static_And_Dynamic_Bounds :=
            Multi_Dimension_Flat_Bounds ("4", Dec_Node);
      pragma Assert (Print_Msg ("Do_Array_Object_Declaration Low " &
                       Array_Name));
      pragma Assert (Print_Msg ("Do_Array_Object_Declaration Low " &
                       Int'Image (Array_Bounds.Low_Static)));
      pragma Assert (Print_Msg ("Do_Array_Object_Declaration High " &
                       Int'Image (Array_Bounds.High_Static)));
      pragma Assert (Print_Node (Dec_Node));
      pragma Assert (Print_Node (Underlying));
      pragma Assert (Print_Msg ("Is Unconstrained " &
                       Boolean'Image (Array_Bounds.Is_Unconstrained)));
      pragma Assert (Print_Msg ("Has static bounds " &
                       Boolean'Image (Array_Bounds.Has_Static_Bounds)));
      Comp_Type        : constant Entity_Id :=
        Component_Type (Target_Type);
      Comp_Irep      : constant Irep :=
        Make_Resolved_I_Type (Comp_Type);

      The_Array    : Irep;
   begin
      if not Array_Bounds.Is_Unconstrained then
         Put_Line ("Do_Array_Object_Declaration - static bounds");
         --  The destination array object is constrained.
         --  Create the array symbol with the target type
         --  but do not perform initialization.
         --  Array initialization is performed below after the if statement.
         declare
            Array_Length     : constant Irep :=
              (if Array_Bounds.Has_Static_Bounds then
                  Integer_Constant_To_Expr
                 (Value           => UI_From_Int
                      (Array_Bounds.High_Static + 1),
                  Expr_Type       => Index_T,
                  Source_Location => Source_Loc)
               else
                  Make_Op_Add
                 (Rhs             => Index_T_One,
                  Lhs             => Array_Bounds.High_Dynamic,
                  Source_Location => Source_Loc,
                  Overflow_Check  => False,
                  I_Type          => Index_T,
                  Range_Check     => False));

            --  If the bounds of the array are static then Array_Length is a
            --  constant and can be used directly to define the size of the
            --  array.  However, if the bounds of the array are not static,
            --  goto requires that a variable, not an expresion,
            --  is used to define the size of the array.
            Arr_Len_Irep : constant Irep :=
              (if Array_Bounds.Has_Static_Bounds then
                  Typecast_If_Necessary
                 (Expr           => Array_Length,
                  New_Type       => Index_T,
                  A_Symbol_Table => Global_Symbol_Table)
               else
                  Make_Symbol_Expr
                 (Source_Location => Source_Loc,
                  I_Type          => Index_T,
                  Range_Check     => False,
                  Identifier      => Array_Name & "_$array_size"));

            Array_Itype      : constant Irep :=
              Make_Array_Type
                (I_Subtype => Comp_Irep,
                 Size      => Arr_Len_Irep);

            Array_Model_Size : constant Irep :=
              Make_Op_Mul
                (Rhs             => Typecast_If_Necessary
                   (Expr           =>
                          ASVAT.Size_Model.Computed_Size (Comp_Type),
                    New_Type       => Index_T,
                    A_Symbol_Table => Global_Symbol_Table),
                 Lhs             => Array_Length,
                 Source_Location => Source_Loc,
                 Overflow_Check  => False,
                 I_Type          => Index_T,
                 Range_Check     => False);

            Decl : constant Irep := Make_Code_Decl
              (Symbol => Arr_Len_Irep,
               Source_Location => Source_Loc);

         begin
            --  Set the ASVAT.Size_Model size for the array.
            ASVAT.Size_Model.Set_Computed_Size
              (Target_Def, Array_Model_Size);

            if not Array_Bounds.Has_Static_Bounds then
               --  The auxilliary variable used to define the array size
               --  has to be declared and initialised.
               --  Declare the variable in the goto code
               Append_Op (Block, Decl);
               --  and assign the array length expression.
               Append_Op (Block,
                          Make_Code_Assign
                            (Rhs             => Typecast_If_Necessary
                               (Expr           => Array_Length,
                                New_Type       => Index_T,
                                A_Symbol_Table => Global_Symbol_Table),
                             Lhs             => Arr_Len_Irep,
                             Source_Location => Source_Loc,
                             I_Type          => Index_T,
                             Range_Check     => False));
            end if;

            The_Array :=
              Make_Symbol_Expr
                (Source_Location => Source_Loc,
                 I_Type          => Array_Itype,
                 Identifier      => Array_Name);

            --  Do not inintalize here, so Init_Expr_Irep = Ireps.Empty.
            Do_Plain_Object_Declaration
              (Block          => Block,
               Object_Sym     => The_Array,
               Object_Name    => Array_Name,
               Object_Def     => Target_Def,
               Init_Expr_Irep => Ireps.Empty);
         end;
      else
         Put_Line ("Do_Array_Object_Declaration - Unconstrained bounds");
         --  The array length, i.e. its goto I_Array_Type,
         --  for an unconstrained array object has to be determined from its
         --  initialization, which must be present.
         Make_Constrained_Array_From_Initialization
           (Block        => Block,
            Array_Name   => Array_Name,
            Init_Expr    => Init_Expr,
            The_Array    => The_Array,
            Array_Bounds => Array_Bounds);

         if Array_Bounds.Is_Unconstrained then
            Report_Unhandled_Node_Empty
              (Init_Expr,
               "Make_Constrained_Array_From_Initialization",
               "Unsupported unconstrained array initialization by " &
                 Node_Kind'Image (Nkind (Init_Expr)));
         end if;

         Array_Object_And_Friends
           (Array_Name   => Array_Name,
            The_Array    => The_Array,
            Array_Bounds => Array_Bounds,
            Array_Node   => Init_Expr,
            Source_Loc   => Source_Loc,
            Block        => Block);

      end if;

      --  The array object should now be in the symbol table.
      pragma Assert (Global_Symbol_Table.Contains (Array_Id));

      --  Now do its initialization, if any.
      if Present (Init_Expr) then
         Put_Line ("Do_Array_Object_Declaration-Initialisation");
         Array_Assignment_Op
           ("2",
            Source_Expr  => Init_Expr,
            N_Dimensions => Number_Dimensions (Target_Type),
            Dest_Bounds  => Array_Bounds,
            Target_Array => The_Array,
            Block        => Block);
      end if;

   end Do_Array_Object_Declaration;

   ---------------------------
   -- All_Dimensions_Static --
   ---------------------------

   function All_Dimensions_Static (The_Array : Entity_Id) return Boolean
     renames Arrays.Low_Level.All_Dimensions_Static;

   ------------------------
   -- Add_Array_Friends --
   ------------------------

   procedure Add_Array_Friends (Array_Name : String;
                                Array_Type : Entity_Id;
                                Param_List : Irep)
   is
      Index_Iter : Node_Id := First_Index (Array_Type);
   begin
      for Dimension in 1 .. Integer (Number_Dimensions (Array_Type)) loop
         pragma Assert (Present (Index_Iter));
         Declare_First_Last_Params
           (Prefix     => Array_Name,
            Dimension  => Dimension,
            Index      => Index_Iter,
            Param_List => Param_List);
         Index_Iter := Next_Index (Index_Iter);
      end loop;
   end Add_Array_Friends;

   ---------------------------
   -- Declare_Array_Friends --
   ---------------------------

   procedure Declare_Array_Friends (Array_Name  : String;
                                    Src_Array   : Node_Id;
                                    Flat_Bounds : Static_And_Dynamic_Bounds;
                                    Block       : Irep)
   is
      pragma Assert (Print_Msg ("Declare_Array_Friends"));
      pragma Assert (Print_Node (Src_Array));
      Source_Location : constant Irep := Get_Source_Location (Block);
      Array_Type      : constant Entity_Id := Etype (Src_Array);
      Src_Node_Kind   : constant Node_Kind := Nkind (Src_Array);
      Src_Is_Object   : constant Boolean :=
        (if Src_Node_Kind in N_Entity then
            Is_Object (Src_Array)
         elsif Src_Node_Kind in N_Has_Entity then
            Is_Object (Entity (Src_Array))
         else
            False);
      Src_I_Type      : constant Irep :=
        Get_Type (Do_Expression (Src_Array));
   begin
      Put_Line ("Declare_Array_Friends");
      Print_Node_Briefly (Src_Array);
      Print_Node_Briefly (Array_Type);
      Put_Line ("Is_Constrained " &
                  Boolean'Image (Is_Constrained (Array_Type)));
      if Ekind (Array_Type) = E_String_Literal_Subtype then
         --  A string literal can only have 1 dimension but
         --  gnat does not give a first index in the atree for string literals.
         declare
            --  The index subtype of a string is Positive
            Str_Index_Type     : constant Irep :=
              Do_Type_Reference (Standard_Positive);
            Str_Lit_Low        : constant Node_Id :=
              String_Literal_Low_Bound (Array_Type);
            Str_Lit_Is_Static  : constant Boolean :=
              Is_OK_Static_Expression (Str_Lit_Low);
            Str_Lit_Low_Static : constant Uint :=
              (if Str_Lit_Is_Static then
                    Expr_Value (Str_Lit_Low)
               else
                  Uint_1);
            Str_Lit_Low_Irep   : constant Irep := Do_Expression (Str_Lit_Low);

            Str_Lit_Length     : constant Uint :=
              String_Literal_Length (Array_Type);

            Str_Lit_High_Irep  : constant Irep :=
              (if Str_Lit_Is_Static then
                  Integer_Constant_To_Expr
                 (Value           =>
                      Str_Lit_Low_Static + Str_Lit_Length - Uint_1,
                  Expr_Type       => Str_Index_Type,
                  Source_Location => Source_Location)
               else
                  Make_Op_Sub
                 (Rhs             =>
                      Integer_Constant_To_Expr
                    (Value           => Uint_1,
                     Expr_Type       => Str_Index_Type,
                     Source_Location => Source_Location),
                  Lhs             => Make_Op_Add
                    (Rhs             =>
                         Integer_Constant_To_Expr
                       (Value           => Str_Lit_Length,
                        Expr_Type       => Str_Index_Type,
                        Source_Location => Source_Location),
                     Lhs             => Str_Lit_Low_Irep,
                     Source_Location => Source_Location,
                     I_Type          => Str_Index_Type),
                  Source_Location => Source_Location,
                  I_Type          => Str_Index_Type));

            Bounds : constant Dimension_Bounds := Dimension_Bounds'
              (Low  => Str_Lit_Low_Irep,
               High => Str_Lit_High_Irep);
         begin
            Declare_First_Last_From_Bounds
              (Prefix     => Array_Name,
               Dimension  => "1",
               Index_Type => Str_Index_Type,
               Bounds     => Bounds,
               Block      => Block);
         end;
      elsif Is_Constrained (Array_Type) then
         Put_Line ("Declare_Array_Friends - Src_Is_Constrained");
         declare
            Index_Iter : Node_Id := First_Index (Array_Type);
         begin
            for Dimension in 1 .. Integer (Number_Dimensions (Array_Type)) loop
               pragma Assert (Present (Index_Iter));
               Declare_First_Last_Vars
                 (Prefix     => Array_Name,
                  Dimension  => Dimension,
                  Index      => Index_Iter,
                  Block      => Block);
               Index_Iter := Next_Index (Index_Iter);
            end loop;
         end;
      elsif Src_Is_Object then
         Put_Line ("Declare_Array_Friends - Src_Is_Object");
         declare
            Src_Entity : constant Entity_Id :=
              (if Src_Node_Kind in N_Entity then
                  Src_Array
               else
                  Entity (Src_Array));
            Src_Name   : constant String := Unique_Name (Src_Entity);
         begin
            Put_Line ("Declare_Array_Friends - Calling " &
                        "Declare_First_Last_From_Object");
            Put_Line (Array_Name);
            Put_Line (Src_Name);
            for Dimension in 1 .. Integer (Number_Dimensions (Array_Type)) loop
               Declare_First_Last_From_Object
                 (Target_Name => Array_Name,
                  Object_Name => Src_Name,
                  Dimension   => Dimension,
                  Block       => Block);
            end loop;
         end;
      elsif Kind (Src_I_Type) = I_Struct_Type then
         Put_Line ("Declare_Array_Friends - Its an unconstrained result");
         --  It is an unconstrained array result.
         declare
            --  Determine the I_Type of the bounds array
            Comp_List  : constant Irep_List :=
              Get_Component (Get_Components (Src_I_Type));
            List_Cur   : constant List_Cursor := List_First (Comp_List);
            Bounds     : constant Irep := List_Element (Comp_List, List_Cur);
            Bounds_Array_Type : constant Irep := Get_Type (Bounds);
            Bounds_Arr : constant Irep := Make_Member_Expr
              (Compound         => Do_Expression (Src_Array),
               Source_Location  => Source_Location,
               I_Type           => Bounds_Array_Type,
               Component_Name   => Array_Struc_Bounds);
            pragma Assert (Print_Msg ("Bounds_Array_Type"));
            pragma Assert (Print_Irep_Func (Bounds_Array_Type));

            --  Get the bounds field from the Fun_Result.
            Bounds_Array        : constant Irep :=
              Fresh_Var_Symbol_Expr (Bounds_Array_Type, "bounds_array");
            pragma Assert (Print_Msg ("Bounds_Array"));
            pragma Assert (Print_Irep_Func (Bounds_Array));

            Index_Iter : Node_Id := First_Index (Array_Type);
         begin
            Put_Line ("Declare_Array_Friends - Loop");
            Print_Irep (Bounds_Array_Type);
            Append_Declare_And_Init
              (Symbol     => Bounds_Array,
               Value      => Bounds_Arr,
               Block      => Block,
               Source_Loc => Source_Location);

            for Dimension in 1 .. Number_Dimensions (Array_Type) loop
               declare
                  Dim_First : constant Irep :=
                    Make_Index_Expr
                      (I_Array         => Bounds_Array,
                       Index           => Integer_Constant_To_Expr
                         (Value           => Bounds_First (Dimension),
                          Expr_Type       => Index_T,
                          Source_Location => Source_Location),
                       Source_Location => Source_Location,
                       I_Type          => Bounds_Component);
                  Dim_Last : constant Irep :=
                    Make_Index_Expr
                      (I_Array         => Bounds_Array,
                       Index           => Integer_Constant_To_Expr
                         (Value           => Bounds_Last (Dimension),
                          Expr_Type       => Index_T,
                          Source_Location => Source_Location),
                       Source_Location => Source_Location,
                       I_Type          => Bounds_Component);
                  Bounds         : constant Dimension_Bounds :=
                    Dimension_Bounds'
                      (Low  => Dim_First,
                       High => Dim_Last);
                  Dim_String_Pre   : constant String := Int'Image (Dimension);
                  Dim_String       : constant String :=
                    Dim_String_Pre (2 .. Dim_String_Pre'Last);

                  Index_I_Type     : constant Irep :=
                    Make_Resolved_I_Type (Etype (Index_Iter));

               begin
                  Declare_First_Last_From_Bounds
                    (Prefix     => Array_Name,
                     Dimension  => Dim_String,
                     Index_Type => Index_I_Type,
                     Bounds     => Bounds,
                     Block      => Block);
               end;
               Index_Iter := Next_Index (Index_Iter);
            end loop;
         end;
      elsif Src_Node_Kind = N_Op_Concat then
         --  The source array expression is a concatination.
         --  Concatinations are one dimensional arrays
         --  An object of an unconstrained type
         --  (if the object is declared without a constraint)
         --  will have a lower bound of Index_Type'First and an upper bound
         --  of Index_Type'First + Flat_Bounds.High
         Put_Line ("Src expr is a concat");
         Print_Node_Subtree (Src_Array);
         Print_Node_Subtree (Array_Type);
--           pragma Assert (False);
         declare
            Index_Type      : constant Irep :=
              Do_Type_Reference (Etype (First_Index (Array_Type)));
            Unconstr_Bounds : constant Dimension_Bounds :=
              Get_Bounds_From_Index (First_Index (Array_Type));
            Bounds : constant Dimension_Bounds :=
              Dimension_Bounds'
                (Low  => Typecast_If_Necessary
                   (Expr           => Unconstr_Bounds.Low,
                    New_Type       => Index_T,
                    A_Symbol_Table => Global_Symbol_Table),
                 High => Typecast_If_Necessary
                   (Expr           => Make_Op_Add
                      (Rhs             => Typecast_If_Necessary
                           (Expr           => Flat_Bounds.High_Dynamic,
                            New_Type       => Index_T,
                            A_Symbol_Table => Global_Symbol_Table),
                       Lhs             => Typecast_If_Necessary
                         (Expr           => Unconstr_Bounds.Low,
                          New_Type       => Index_T,
                          A_Symbol_Table => Global_Symbol_Table),
                       Source_Location => Source_Location,
                       I_Type          => Index_T),
                    New_Type       => Index_T,
                    A_Symbol_Table => Global_Symbol_Table));
         begin
            Declare_First_Last_From_Bounds
              (Prefix     => Array_Name,
               Dimension  => "1",
               Index_Type => Index_Type,
               Bounds     => Bounds,
               Block      => Block);
         end;
      else
         Report_Unhandled_Node_Empty
           (N        => Array_Type,
            Fun_Name => "Declare_Array_Friends",
            Message  =>
              "Cannot create First and Last from unconstrained array");
      end if;
   end Declare_Array_Friends;

   ----------------------------------------
   -- Declare_First_And_Last_From_Bounds --
   ----------------------------------------

   procedure Declare_First_Last_From_Bounds (Prefix     : String;
                                             Dimension  : String;
                                             Index_Type : Irep;
                                             Bounds     : Dimension_Bounds;
                                             Block      : Irep)
   is
      Source_Loc      : constant Irep := Internal_Source_Location;
      First_Name      : constant String :=
        Prefix & First_Var_Str & Dimension;
      First_Name_Id   : constant Symbol_Id := Intern (First_Name);
      Last_Name       : constant String :=
        Prefix & Last_Var_Str & Dimension;
      Last_Name_Id    : constant Symbol_Id := Intern (Last_Name);

      First_Sym : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Index_Type,
           Range_Check     => False,
           Identifier      => First_Name);
      Last_Sym : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Index_Type,
           Range_Check     => False,
           Identifier      => Last_Name);

      First_Val : constant Irep :=
        Typecast_If_Necessary
          (Expr           => Bounds.Low,
           New_Type       => Index_Type,
           A_Symbol_Table => Global_Symbol_Table);

      Last_Val : constant Irep :=
        Typecast_If_Necessary
          (Expr           => Bounds.High,
           New_Type       => Index_Type,
           A_Symbol_Table => Global_Symbol_Table);
   begin
      --  Add the first and last variables to the symbol table.
      New_Object_Symbol_Entry
        (Object_Name       => First_Name_Id,
         Object_Type       => Index_Type,
         Object_Init_Value => Bounds.Low,
         A_Symbol_Table    => Global_Symbol_Table);
      New_Object_Symbol_Entry
        (Object_Name       => Last_Name_Id,
         Object_Type       => Index_Type,
         Object_Init_Value => Bounds.High,
         A_Symbol_Table    => Global_Symbol_Table);

      --  Declare and assign values in goto code.
      Append_Declare_And_Init
        (Symbol     => First_Sym,
         Value      => First_Val,
         Block      => Block,
         Source_Loc => Source_Loc);
      Append_Declare_And_Init
        (Symbol     => Last_Sym,
         Value      => Last_Val,
         Block      => Block,
         Source_Loc => Source_Loc);
   end Declare_First_Last_From_Bounds;

   -----------------------------------------
   -- Declare_First_And_Last_From_Object --
   -----------------------------------------

   procedure Declare_First_Last_From_Object (Target_Name : String;
                                             Object_Name : String;
                                             Dimension   : Positive;
                                             Block       : Irep)
   is
      Dim_String_Pre  : constant String := Integer'Image (Dimension);
      Dim_String      : constant String :=
        Dim_String_Pre (2 .. Dim_String_Pre'Last);
      Source_Loc      : constant Irep := Internal_Source_Location;
      Target_First    : constant String :=
        Target_Name & First_Var_Str & Dim_String;
      Target_First_Id : constant Symbol_Id := Intern (Target_First);
      Target_Last     : constant String :=
        Target_Name & Last_Var_Str & Dim_String;
      Target_Last_Id  : constant Symbol_Id := Intern (Target_Last);

      Object_First    : constant String :=
        Object_Name & First_Var_Str & Dim_String;
      Object_First_Id : constant Symbol_Id := Intern (Object_First);
      Object_Last     : constant String :=
        Object_Name & Last_Var_Str & Dim_String;
      Object_Last_Id  : constant Symbol_Id := Intern (Object_Last);

      pragma Assert (Global_Symbol_Table.Contains (Object_First_Id) and
                     Global_Symbol_Table.Contains (Object_Last_Id));

      Index_Type : constant Irep :=
        Global_Symbol_Table (Object_First_Id).SymType;

      Target_First_Sym : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Index_Type,
           Range_Check     => False,
           Identifier      => Target_First);
      Target_Last_Sym : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Index_Type,
           Range_Check     => False,
           Identifier      => Target_Last);

      Object_First_Sym : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Index_Type,
           Range_Check     => False,
           Identifier      => Object_First);
      Object_Last_Sym : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Index_Type,
           Range_Check     => False,
           Identifier      => Object_Last);

   begin
      --  Add the first and last variables to the symbol table.
      New_Object_Symbol_Entry
        (Object_Name       => Target_First_Id,
         Object_Type       => Index_Type,
         Object_Init_Value => Object_First_Sym,
         A_Symbol_Table    => Global_Symbol_Table);
      New_Object_Symbol_Entry
        (Object_Name       => Target_Last_Id,
         Object_Type       => Index_Type,
         Object_Init_Value => Object_Last_Sym,
         A_Symbol_Table    => Global_Symbol_Table);

      --  Declare and assign values in goto code.
      Append_Declare_And_Init
        (Symbol     => Target_First_Sym,
         Value      => Object_First_Sym,
         Block      => Block,
         Source_Loc => Source_Loc);
      Append_Declare_And_Init
        (Symbol     => Target_Last_Sym,
         Value      => Object_Last_Sym,
         Block      => Block,
         Source_Loc => Source_Loc);
   end Declare_First_Last_From_Object;

   -----------------------------------
   -- Declare_First_And_Last_Params --
   -----------------------------------

   procedure Declare_First_Last_Params (Prefix     : String;
                                        Dimension  : Positive;
                                        Index      : Node_Id;
                                        Param_List : Irep)
   is
      Source_Loc      : constant Irep := Get_Source_Location (Index);
      Number_Str_Raw  : constant String :=
        Integer'Image (Dimension);
      Number_Str      : constant String :=
        Number_Str_Raw (2 .. Number_Str_Raw'Last);
      First_Name      : constant String :=
        Prefix & First_Var_Str & Number_Str;
      First_Name_Id   : constant Symbol_Id := Intern (First_Name);
      Last_Name       : constant String :=
        Prefix & Last_Var_Str & Number_Str;
      Last_Name_Id    : constant Symbol_Id := Intern (Last_Name);

      Index_Type : constant Entity_Id :=
        Base_Type (Etype (Index));
      Index_Id : constant Symbol_Id :=
        Intern (Unique_Name (Index_Type));
      pragma Assert (Global_Symbol_Table.Contains (Index_Id));

      Type_Irep : constant Irep :=
        Do_Type_Reference (Index_Type);

      --  Formal parameters.
      First_Irep : constant Irep := Make_Code_Parameter
        (Source_Location => Source_Loc,
         I_Type => Type_Irep,
         Identifier => First_Name,
         Base_Name => First_Name,
         This => False,
         Default_Value => Ireps.Empty);

      Last_Irep : constant Irep := Make_Code_Parameter
        (Source_Location => Source_Loc,
         I_Type => Type_Irep,
         Identifier => Last_Name,
         Base_Name => Last_Name,
         This => False,
         Default_Value => Ireps.Empty);
   begin
      --  Add the parameters to the symbol table.
      New_Parameter_Symbol_Entry
        (Name_Id        => First_Name_Id,
         BaseName       => First_Name,
         Symbol_Type    => Type_Irep,
         A_Symbol_Table => Global_Symbol_Table);

      New_Parameter_Symbol_Entry
        (Name_Id        => Last_Name_Id,
         BaseName       => Last_Name,
         Symbol_Type    => Type_Irep,
         A_Symbol_Table => Global_Symbol_Table);

      --  Append the parameters to the parameter list.
      Append_Parameter (Param_List, First_Irep);
      Append_Parameter (Param_List, Last_Irep);

   end Declare_First_Last_Params;

   ---------------------------------
   -- Declare_First_And_Last_Vars --
   ---------------------------------

   procedure Declare_First_Last_Vars (Prefix    : String;
                                      Dimension : Positive;
                                      Index     : Node_Id;
                                      Block      : Irep)
   is
      Number_Str_Raw  : constant String :=
        Integer'Image (Dimension);
      Number_Str      : constant String :=
        Number_Str_Raw (2 .. Number_Str_Raw'Last);

      Index_Type : constant Entity_Id :=
        Base_Type (Etype (Index));

      Bounds : constant Dimension_Bounds := Get_Bounds_From_Index (Index);
   begin
      Put_Line ("Declare_First_Last_Vars");
      Print_Node_Briefly (Index);
      Print_Irep (Bounds.Low);
      Print_Irep (Bounds.High);
      Declare_First_Last_From_Bounds
        (Prefix     => Prefix,
         Dimension  => Number_Str,
         Index_Type => Do_Type_Reference (Index_Type),
         Bounds     => Bounds,
         Block      => Block);
   end Declare_First_Last_Vars;

   --------------------------------
   -- Do_Aggregate_Literal_Array --
   --------------------------------

   function Do_Aggregate_Literal_Array (N : Node_Id) return Irep is
      Source_Location   : constant Irep := Get_Source_Location (N);
      Positional_Assoc  : constant Boolean := Present (Expressions (N));
      Has_Static_Bounds : constant Boolean :=
        Is_OK_Static_Range (Aggregate_Bounds (N));
      Aggregate_Subtype : constant Entity_Id := Etype (N);
      New_Name          : constant String := Fresh_Var_Name ("aggregate_");
      Aggregate_Obj     : constant String := New_Name & "_obj";
      Aggregate_Func    : constant String := New_Name & "_fun";
--        Aggregate_Loop    : constant String := New_Name & "_loop";
      Subtype_Irep      : constant Irep :=
        Do_Type_Reference (Aggregate_Subtype);
      Component_Irep    : constant Irep :=
        Make_Resolved_I_Type (Component_Type (Aggregate_Subtype));
      Obj_Irep          : constant Irep := Make_Symbol_Expr
        (Source_Location => Source_Location,
         I_Type          => Subtype_Irep,
         Range_Check     => False,
         Identifier      => Aggregate_Obj);
      Func_Irep         : constant Irep :=
        Make_Code_Type (Parameters  => Make_Parameter_List,  -- No parameters.
                        Ellipsis    => False,
                        Return_Type => Subtype_Irep,
                        Inlined     => False,
                        Knr         => False);
      Result_Block      : constant Irep := Make_Code_Block (Source_Location);
      Obj_Dec           : constant Irep := Make_Code_Decl
        (Symbol          => Obj_Irep,
         Source_Location => Source_Location,
         I_Type          => Subtype_Irep,
         Range_Check     => False);

   begin
      --  First add the aggregate array object to the symbol table.
      New_Object_Symbol_Entry
        (Object_Name       => Intern (Aggregate_Obj),
               Object_Type       => Subtype_Irep,
               Object_Init_Value => Ireps.Empty,
               A_Symbol_Table    => Global_Symbol_Table);

      --  Make the body of the function that builds the aggregate
      --  First the declaration of the aggregate array;
      Append_Op (Result_Block, Obj_Dec);

      if Has_Static_Bounds then
         declare
            Low_Expr  : constant Uint :=
              Expr_Value (Low_Bound  (Aggregate_Bounds (N)));
            High_Expr : constant Uint :=
              Expr_Value (High_Bound (Aggregate_Bounds (N)));
            Low  : constant Int := UI_To_Int (Low_Expr);
            High : constant Int := UI_To_Int (High_Expr);
         begin
            Put_Line ("Do_Aggregate_Literal_Array");
            Put_Line ("Low " & Int'Image (Low));
            Put_Line ("High" & Int'Image (High));
            Print_Node_Briefly (Aggregate_Bounds (N));
            if Positional_Assoc then
               Array_Static_Positional
                 (Block      => Result_Block,
                  Low_Bound  => 0,
                  High_Bound => High - Low,
                  N          => N,
                  Target     => Obj_Irep,
                  Comp_Type  => Component_Irep);
            elsif Present (Component_Associations (N)) then
               --  Named associations.
               Array_Static_Named_Assoc
                 (Block      => Result_Block,
                  Low_Bound  => 0,
                  High_Bound => High - Low,
                  N          => N,
                  Target     => Obj_Irep,
                  Comp_Type  => Component_Irep);
            else
               Report_Unhandled_Node_Empty
                 (N        => N,
                  Fun_Name => "Do_Aggregate_Array_Literal",
                  Message  =>
                 "Aggregate has neither Positional or Named arguments");
            end if;
         end;
      else
         Report_Unhandled_Node_Empty
           (N        => N,
            Fun_Name => "Do_Aggregate_Array_Literal",
            Message  => "Aggregates with non-static bounds unsupported");
         declare
            Bounds : constant Dimension_Bounds :=
              Get_Dimension_Bounds (N, 1, Aggregate_Bounds (N));
         begin
            if Positional_Assoc then
               Put_Line ("Dynamic Positional");
               Array_Dynamic_Positional
                 (Block      => Result_Block,
                  Low_Bound  => Index_T_Zero,
                  High_Bound => Make_Zero_Index
                    (Index    => Bounds.High,
                     First    => Bounds.Low,
                     Location => Source_Location),
                  N          => N,
                  Target     => Obj_Irep,
                  Comp_Type  => Component_Irep);
            else
               Put_Line ("Dynamic Named");
               Array_Dynamic_Named_Assoc
                 (Block      => Result_Block,
                  Low_Bound  => Index_T_Zero,
                  High_Bound => Make_Zero_Index
                    (Index    => Bounds.High,
                     First    => Bounds.Low,
                     Location => Source_Location),
                  N          => N,
                  Target     => Obj_Irep,
                  Comp_Type  => Component_Irep);
            end if;
         end;
      end if;

      --  Now add the return statement.
      Append_Op (Result_Block,
                 Make_Code_Return (Return_Value    => Obj_Irep,
                                   Source_Location => Source_Location));
      --  Create the aggregate function from the body
      --  and return a call to the function.
      declare
         Aggregate_Func_Symbol : constant Symbol :=
           New_Function_Symbol_Entry
             (Name           => Aggregate_Func,
              Symbol_Type    => Func_Irep,
              Value          => Result_Block,
              A_Symbol_Table => Global_Symbol_Table);
         Func_Call : constant Irep :=
           Make_Side_Effect_Expr_Function_Call
             (Arguments       => Make_Argument_List,  -- Null arg list.
              I_Function      => Symbol_Expr (Aggregate_Func_Symbol),
              Source_Location => Source_Location,
              I_Type          => Subtype_Irep,
              Range_Check     => False);
      begin
         return Func_Call;
      end;
   end Do_Aggregate_Literal_Array;

   -----------------------
   -- Do_String_Literal --
   -----------------------

   function Do_String_Literal (N : Node_Id) return Irep is
      Source_Location   : constant Irep := Get_Source_Location (N);
      --  String literals are stored in string constants table described
      --  Stringst.
      --  Their lower bound is always 1 and therefore the string length
      --  is also the string litera['s high bound.
      Str_Id            : constant String_Id := Strval (N);
      Str_Lit_High      : constant Nat := String_Length (Str_Id);
      Str_Lit_Size_Irep : constant Irep :=
        Integer_Constant_To_Expr
          (Value           => UI_From_Int (Str_Lit_High - 1),
           Expr_Type       => Index_T,
           Source_Location => Source_Location);
      --  To Do: This needs to changed to Make_Char_Type ...
      Component_Irep    : constant Irep := Make_Unsignedbv_Type (8);
      Str_Subtype       : constant Irep :=
        Make_Array_Type
          (I_Subtype => Component_Irep,
           Size      => Str_Lit_Size_Irep);

      New_Name          : constant String := Fresh_Var_Name ("string_");
      String_Obj        : constant String := New_Name & "_obj";
      String_Func       : constant String := New_Name & "_fun";
      Obj_Irep          : constant Irep := Make_Symbol_Expr
        (Source_Location => Source_Location,
         I_Type          => Str_Subtype,
         Range_Check     => False,
         Identifier      => String_Obj);
      Func_Irep         : constant Irep :=
        Make_Code_Type (Parameters  => Make_Parameter_List,  -- No parameters.
                        Ellipsis    => False,
                        Return_Type => Str_Subtype,
                        Inlined     => False,
                        Knr         => False);
      Result_Block      : constant Irep := Make_Code_Block (Source_Location);
      Obj_Dec           : constant Irep := Make_Code_Decl
        (Symbol          => Obj_Irep,
         Source_Location => Source_Location,
         I_Type          => Str_Subtype,
         Range_Check     => False);
   begin
      --  First add the array object for the string to the symbol table.
      New_Object_Symbol_Entry
        (Object_Name       => Intern (String_Obj),
               Object_Type       => Str_Subtype,
               Object_Init_Value => Ireps.Empty,
               A_Symbol_Table    => Global_Symbol_Table);

      --  Make the body of the function that builds the aggregate
      --  First the declaration of the aggregate array;
      Append_Op (Result_Block, Obj_Dec);

      Update_Array_From_String_Literal
        (Block        => Result_Block,
         Str_Lit      => N,
         Dest_Array   => Obj_Irep);

      --  Now add the return statement.
      Append_Op (Result_Block,
                 Make_Code_Return (Return_Value    => Obj_Irep,
                                   Source_Location => Source_Location));
      --  Create the aggregate function from the body
      --  and return a call to the function.
      declare
         Str_Func_Symbol : constant Symbol :=
           New_Function_Symbol_Entry
             (Name           => String_Func,
              Symbol_Type    => Func_Irep,
              Value          => Result_Block,
              A_Symbol_Table => Global_Symbol_Table);
         Func_Call : constant Irep :=
           Make_Side_Effect_Expr_Function_Call
             (Arguments       => Make_Argument_List,  -- Null arg list.
              I_Function      => Symbol_Expr (Str_Func_Symbol),
              Source_Location => Source_Location,
              I_Type          => Str_Subtype,
              Range_Check     => False);
      begin
         return Func_Call;
      end;
   end Do_String_Literal;

   ----------------------
   -- Do_Array_Subtype --
   ----------------------

   function Do_Array_Subtype (Subtype_Node : Node_Id;
                              The_Entity   : Entity_Id) return Irep
   is
   begin
      Put_Line ("Do_Array_Subtype");
      Print_Node_Briefly (Subtype_Node);
      Print_Node_Briefly (The_Entity);
      Put_Line ("Is_Constrained " &
                  Boolean'Image (Is_Constrained (The_Entity)));
      return (if Is_Constrained (The_Entity) then
                 Make_Constrained_Array_Subtype
                (Declaration    => Subtype_Node)
              else
                 Make_Unconstrained_Array_Subtype
                (Declaration    => Subtype_Node,
                 Component_Type => Component_Type (Etype (The_Entity))));
   end Do_Array_Subtype;

   -------------------------------------
   -- Do_Constrained_Array_Definition --
   -------------------------------------

   function Do_Constrained_Array_Definition (N     : Node_Id) return Irep is
      --  The array type declaration node is the  parent of the
      --  array_definition node.
   begin
         Put_Line ("Do_Constrained_Array_Definition");
         Print_Node_Briefly (N);
      return
        (Make_Constrained_Array_Subtype
           (Declaration    => Parent (N)));
   end Do_Constrained_Array_Definition;

   ---------------------------------------
   -- Do_Unconstrained_Array_Definition --
   ---------------------------------------

   function Do_Unconstrained_Array_Definition (N     : Node_Id) return Irep is
      --  The array type declaration node is the  parent of the
      --  array_definition node.
     (Make_Unconstrained_Array_Subtype
        (Declaration    => Parent (N),
         Component_Type =>
           (Component_Type (Defining_Identifier (Parent (N))))));

--     function Get_Data_Component_From_Type (Array_Struct_Type : Irep)
--                                            return Irep;
--     function Get_Data_Component_From_Type (Array_Struct_Type : Irep)
--                                            return Irep
--     is
--        Struct_Component : constant Irep_List :=
--          Get_Component (Get_Components (Array_Struct_Type));
--        Last_Cursor :  constant List_Cursor :=
--          List_Next (Struct_Component,
--                     List_Next (Struct_Component,
--                       List_First (Struct_Component)));
--     begin
--        return List_Element (Struct_Component, Last_Cursor);
--     end Get_Data_Component_From_Type;

--     function Get_Data_Component (Array_Struct : Irep;
--                                  A_Symbol_Table : Symbol_Table)
--                                  return Irep;
--     function Get_Data_Component (Array_Struct : Irep;
--                                  A_Symbol_Table : Symbol_Table)
--                                  return Irep
--     is
--        Array_Struct_Type : constant Irep :=
--          Follow_Symbol_Type (Get_Type (Array_Struct), A_Symbol_Table);
--     begin
--        return Get_Data_Component_From_Type (Array_Struct_Type);
--     end Get_Data_Component;

--     function Get_Data_Member (Array_Struct : Irep;
--                               A_Symbol_Table : Symbol_Table)
--                               return Irep;
--     function Get_Data_Member (Array_Struct : Irep;
--                               A_Symbol_Table : Symbol_Table)
--                               return Irep
--     is
--        Data_Member : constant Irep :=
--          Get_Data_Component (Array_Struct, A_Symbol_Table);
--     begin
--        return Make_Member_Expr (Compound         => Array_Struct,
--                                 Source_Location  =>
--                                    Internal_Source_Location,
--                                 Component_Number => 2,
--                                 I_Type           =>
--                                   Get_Type (Data_Member),
--                                 Component_Name   =>
--                                   Get_Name (Data_Member));
--     end Get_Data_Member;

   -------------------------
   -- Do_Array_Assignment --
   -------------------------

   procedure Do_Array_Assignment (Block : Irep; N : Node_Id)
   is
--        Source_Loc : constant Irep := Get_Source_Location (N);
      --  The LHS must be a constrained array.
      LHS_Node   : constant Node_Id := Name (N);
      RHS_Node   : constant Node_Id := Expression (N);
      LHS_Kind   : constant Node_Kind := Nkind (LHS_Node);
      RHS_Kind   : constant Node_Kind := Nkind (RHS_Node);
      LHS_Type   : constant Node_Id := Underlying_Type (Etype (LHS_Node));
      RHS_Type   : constant Node_Id := Underlying_Type (Etype (RHS_Node));
   begin
      Put_Line ("Do_Array_Assignment");
      Print_Node_Briefly (LHS_Node);
      Print_Node_Briefly (RHS_Node);
      Put_Line (Node_Kind'Image (LHS_Kind));
      Put_Line (Node_Kind'Image (RHS_Kind));
      Print_Node_Briefly (LHS_Type);
      Print_Node_Briefly (RHS_Type);
      Put_Line ("Forwards_Ok " & Boolean'Image (Forwards_OK (N)));
      Put_Line ("Backwards_Ok " & Boolean'Image (Backwards_OK (N)));
      Put_Line ("RHS is static expr " &
                  Boolean'Image (Is_OK_Static_Expression (RHS_Node)));
      if LHS_Kind /= N_Slice and
        RHS_Kind not in N_Slice | N_Aggregate | N_Op_Concat
      then
         Put_Line ("Assignment without temporary");
         Do_Array_Assignment_Op
           (Block       => Block,
            Destination => Do_Expression (LHS_Node),
            Dest_Type   => LHS_Type,
            Source_Expr => RHS_Node);
      else
         Put_Line ("Temporary required");
         --  LHS should be constrained
         Put_Line ("LHS constrained " &
                     Boolean'Image (Is_Constrained (LHS_Type)));
         Put_Line ("LHS type in symbol table " &
                     Boolean'Image (Global_Symbol_Table.Contains
                     (Intern (Unique_Name (LHS_Type)))));
         --  Declare a temporary array to construct the result
         declare
            LHS_I_Type         : constant Irep := Do_Type_Reference (LHS_Type);
            Temp_Array         : constant Irep :=
              Fresh_Var_Symbol_Expr (LHS_I_Type, "temp_arr_ass");
            Temp_Array_Bounds  : constant Static_And_Dynamic_Bounds :=
              Multi_Dimension_Flat_Bounds ("99", LHS_Node);
            pragma Assert (Print_Msg
                           ("Do_Array_Assignment - Got temp array bounds"));
            Dest_Bounds        : constant Static_And_Dynamic_Bounds :=
              Zero_Based_Bounds (LHS_Node);
            pragma Assert (Print_Msg
                           ("Do_Array_Assignment - Got dest bounds"));
         begin
            Append_Op (Block,
                       Make_Code_Decl
                         (Symbol          => Temp_Array,
                          Source_Location => Get_Source_Location (N)));
            --  Assign to the temporary array
            Do_Array_Assignment_Op
              (Block       => Block,
               Destination => Temp_Array,
               Dest_Type   => LHS_Type,
               Source_Expr => RHS_Node);

            --  Now assign the temporary array to the desination
            Assign_Array
              (Block         => Block,
               Destination   => Do_Expression (LHS_Node),
               Dest_Bounds   => Dest_Bounds,
               Source        => Temp_Array,
               Source_Bounds => Temp_Array_Bounds);
         end;
      end if;
      Report_Unhandled_Node_Empty
        (N        => N,
         Fun_Name => "Do_Array_Assignment",
         Message  => "Testing");
   end Do_Array_Assignment;

   --  The following function builds a generalised array assignment
   --  dest := src_1 & src_2 & .. & src_n         for $n$ greater or equal to 1
   --  where each src_i may overlap with dest
   --  and sum_size is the sum of the slice sizes
   --  (which is why we copy each src_i to a temporary before copying to dest)
   --  Let ArrT := struct { int first; int last; T* data; }
   ----------------------------------------------------------------------------
   --  void concat_assign(ArrT dest, ArrT src_1, ArrT src_2, .., ArrT src_n) {
   --    dest_temp = (T*)malloc(sum_size * sizeof(T));
   --    offset_step = 0;
   --    slice_size = src_1.last - src_1.first + 1;
   --    memcpy(dest_temp + offset_step, src_1.data, slice_size * sizeof(T));
   --    offset_step += slice_size;
   --
   --    slice_size = src_2.last - src_2.first + 1;
   --    memcpy(dest_temp + offset_step, src_2.data, slice_size * sizeof(T));
   --    offset_step += slice_size;
   --    ...
   --    slice_size = src_n.last - src_n.first + 1;
   --    memcpy(dest_temp + offset_step, src_n.data, slice_size * sizeof(T));
   --    offset_step += slice_size;
   --
   --    memcpy(dest.data, dest_temp, sum_size * sizeof(T));
   --  }
   ----------------------------------------------------------------------------
   --  Once the function is constructed it returns a function call (expression)
   --  concat_assign(dest, src_1, src_2, .., src_n);
--     function Do_Array_Assignment (N : Node_Id) return Irep
--     is
--        --  We assume the lhs is allocated
--        LHS_Node : constant Node_Id := Name (N);
--        RHS_Node : constant Node_Id := Expression (N);
--
--        Source_Loc : constant Irep := Get_Source_Location (N);
--        Ret_Type : constant Irep := Make_Void_Type;
--        RHS_Arrays : constant Irep_Array := Do_RHS_Array_Assign (RHS_Node);
--        Result_Type : constant Irep := Do_Type_Reference (Etype (LHS_Node));
--        Concat_Params : constant Irep := Make_Parameter_List;
--        Concat_Arguments : constant Irep := Make_Argument_List;
--        Elem_Type_Ent : constant Entity_Id :=
--          Get_Non_Array_Component_Type (LHS_Node);
--        Element_Type : constant Irep := Do_Type_Reference (Elem_Type_Ent);
--        --  Unique name given by Build_Function.
--        Function_Name : constant String := "concat_assign";
--
--        Destination : constant Irep :=
--          Create_Fun_Parameter (Fun_Name        => Function_Name,
--                                Param_Name      => "dest_array",
--                                Param_Type      => Result_Type,
--                                Param_List      => Concat_Params,
--                                A_Symbol_Table  => Global_Symbol_Table,
--                                Source_Location => Source_Loc);
--
--        function Build_Array_Params return Irep_Array;
--        function Build_Concat_Assign_Body return Irep;
--
--        function Build_Array_Params return Irep_Array
--        is
--           Result_Array : Irep_Array (RHS_Arrays'Range);
--        begin
--           for I in RHS_Arrays'Range loop
--              Result_Array (I) :=
--                Create_Fun_Parameter (Fun_Name        => Function_Name,
--                                      Param_Name      => "array_rhs",
--                                      Param_Type      => Result_Type,
--                                      Param_List      => Concat_Params,
--                                      A_Symbol_Table  => Global_Symbol_Table,
--                                      Source_Location => Source_Loc);
--           end loop;
--           return Result_Array;
--        end Build_Array_Params;
--
--        function Build_Concat_Assign_Body return Irep
--        is
--           Slices : constant Irep_Array := Build_Array_Params;
--           Result_Block : constant Irep :=
--             Make_Code_Block (Source_Loc, CProver_Nil_T);
--           Dest_Symbol : constant Irep := Param_Symbol (Destination);
--           PElement_Type : constant Irep :=
--             Make_Pointer_Type (Element_Type, Pointer_Type_Width);
--
--           Dest_Data : constant Irep := Get_Data_Member
--              (Dest_Symbol,
--               Global_Symbol_Table);
--           Current_Offset : constant Irep :=
--             Fresh_Var_Symbol_Expr (CProver_Size_T, "offset_step");
--
--           Void_Ptr_Type : constant Irep :=
--             Make_Pointer_Type (I_Subtype => Make_Void_Type,
--                                Width     => Pointer_Type_Width);
--           Memcpy_Lhs : constant Irep :=
--             Fresh_Var_Symbol_Expr (Void_Ptr_Type, "memcpy_lhs");
--           Zero : constant Irep :=
--             Build_Index_Constant (Value      => 0,
--                                   Source_Loc => Source_Loc);
--           EType_Size : constant Uint := Esize (Elem_Type_Ent);
--
--           Sum_Size_Var : constant Irep :=
--             Fresh_Var_Symbol_Expr (CProver_Size_T, "sum_size");
--           Dest_Temp_Pre_Alloc : constant Irep :=
--             Make_Malloc_Function_Call_Expr
--                (Num_Elem          => Sum_Size_Var,
--                 Element_Type_Size => EType_Size,
--                 Source_Loc        => Source_Loc);
--           Dest_Temp_Alloc : constant Irep :=
--             Typecast_If_Necessary (Dest_Temp_Pre_Alloc, PElement_Type,
--                                    Global_Symbol_Table);
--           Dest_Temp : constant Irep :=
--             Fresh_Var_Symbol_Expr (PElement_Type, "dest_temp");
--
--           procedure Build_Sum_Size (Ith_Slice : Irep);
--
--           procedure Build_Sum_Size (Ith_Slice : Irep) is
--              Source_I_Symbol : constant Irep := Param_Symbol (Ith_Slice);
--              Slice_Size : constant Irep :=
--                Build_Array_Size (Source_I_Symbol);
--              Size_Increment : constant Irep :=
--                Make_Op_Add
--                  (Rhs             =>
--                  Typecast_If_Necessary (Slice_Size, CProver_Size_T,
--                                 Global_Symbol_Table),
--                             Lhs             => Sum_Size_Var,
--                             Source_Location => Source_Loc,
--                             Overflow_Check  => False,
--                             I_Type          => CProver_Size_T);
--           begin
--              Append_Op (Result_Block,
--                         Make_Code_Assign (Rhs             => Size_Increment,
--                                           Lhs             => Sum_Size_Var,
--                                           Source_Location => Source_Loc));
--           end Build_Sum_Size;
--
--           procedure Process_Slice (Ith_Slice : Irep);
--
--        --  Allocate a temporary, memcpy into the temporary, compute offset
--           --  for destination, memcpy into the destination
--           procedure Process_Slice (Ith_Slice : Irep)
--           is
--              Source_I_Symbol : constant Irep := Param_Symbol (Ith_Slice);
--              Slice_Size : constant Irep :=
--                Build_Array_Size (Source_I_Symbol);
--              Slice_Size_Var : constant Irep :=
--                Fresh_Var_Symbol_Expr (CProver_Size_T, "slice_size");
--              Offset_Dest : constant Irep :=
--                Make_Op_Add (Rhs             => Current_Offset,
--                             Lhs             => Dest_Temp,
--                             Source_Location => Source_Loc,
--                             Overflow_Check  => False,
--                             I_Type          => PElement_Type);
--              Left_Data : constant Irep := Get_Data_Member (Source_I_Symbol,
--                                                       Global_Symbol_Table);
--
--              Memcpy_Fin : constant Irep :=
--                Make_Memcpy_Function_Call_Expr (
--                                            Destination       => Offset_Dest,
--                                            Source            => Left_Data,
--                                        Num_Elem          => Slice_Size_Var,
--                                            Element_Type_Size => EType_Size,
--                                            Source_Loc        => Source_Loc);
--              Size_Increment : constant Irep :=
--                Make_Op_Add (Rhs             => Slice_Size_Var,
--                             Lhs             => Current_Offset,
--                             Source_Location => Source_Loc,
--                             I_Type          => CProver_Size_T);
--           begin
--              Append_Op (Result_Block,
--                         Make_Code_Assign (Rhs             => Slice_Size,
--                                           Lhs             => Slice_Size_Var,
--                                           Source_Location => Source_Loc));
--              Append_Op (Result_Block,
--                         Make_Code_Assign (Rhs             => Memcpy_Fin,
--                                           Lhs             => Memcpy_Lhs,
--                                           Source_Location => Source_Loc));
--              Append_Op (Result_Block,
--                         Make_Code_Assign (Rhs             => Size_Increment,
--                                           Lhs             => Current_Offset,
--                                           Source_Location => Source_Loc));
--           end Process_Slice;
--
--           Memcpy_Dest : constant Irep :=
--             Make_Memcpy_Function_Call_Expr (
--                                             Destination       => Dest_Data,
--                                             Source            => Dest_Temp,
--                                          Num_Elem          => Sum_Size_Var,
--                                             Element_Type_Size => EType_Size,
--                                           Source_Loc        => Source_Loc);
--        begin
--           Append_Op (Result_Block,
--                      Make_Code_Assign (Rhs             => Zero,
--                                        Lhs             => Current_Offset,
--                                        Source_Location => Source_Loc));
--           Append_Op (Result_Block,
--                      Make_Code_Assign (Rhs             =>
--                                          Typecast_If_Necessary (Zero,
--                                       CProver_Size_T, Global_Symbol_Table),
--                                    Lhs             => Sum_Size_Var,
--                                    Source_Location => Source_Loc));
--           for I in Slices'Range loop
--              Build_Sum_Size (Slices (I));
--           end loop;
--           Append_Op (Result_Block,
--                      Make_Code_Assign (Rhs             => Dest_Temp_Alloc,
--                                        Lhs             => Dest_Temp,
--                                        Source_Location => Source_Loc));
--           for I in Slices'Range loop
--              Process_Slice (Slices (I));
--           end loop;
--           Append_Op (Result_Block,
--                      Make_Code_Assign (Rhs             => Memcpy_Dest,
--                                        Lhs             => Memcpy_Lhs,
--                                        Source_Location => Source_Loc));
--           return Result_Block;
--        end Build_Concat_Assign_Body;
--
--        Func_Symbol : constant Symbol :=
--          Build_Function (Name           => Function_Name,
--                          RType          => Ret_Type,
--                          Func_Params    => Concat_Params,
--                          FBody          => Build_Concat_Assign_Body,
--                          A_Symbol_Table => Global_Symbol_Table);
--
--        Func_Call : constant Irep :=
--          Make_Side_Effect_Expr_Function_Call (
--                                    Arguments       => Concat_Arguments,
--                               I_Function      => Symbol_Expr (Func_Symbol),
--                                 Source_Location => Source_Loc,
--                                    I_Type          => Ret_Type);
--        Concat_Lhs : constant Irep :=
--          Fresh_Var_Symbol_Expr (Ret_Type, "concat_Lhs");
--     begin
--        Append_Argument (Concat_Arguments,
--                         Do_Expression (LHS_Node));
--        for I in RHS_Arrays'Range loop
--           Append_Argument (Concat_Arguments,
--                            RHS_Arrays (I));
--        end loop;
--
--        return Make_Code_Assign (Rhs             => Func_Call,
--                                 Lhs             => Concat_Lhs,
--                                 Source_Location => Source_Loc);
--     end Do_Array_Assignment;

   function Do_RHS_Array_Assign (N : Node_Id) return Irep_Array
   is
   begin
      if not (Nkind (N) = N_Op_Concat) then
         return (1 => Do_Expression (N));
      end if;
      if Nkind (Right_Opnd (N)) = N_Op_Concat then
         if Nkind (Left_Opnd (N)) = N_Op_Concat then
            return Do_RHS_Array_Assign (Left_Opnd (N))
              & Do_RHS_Array_Assign (Right_Opnd (N));
         else
            return (1 => Do_Expression (Left_Opnd (N)))
              & Do_RHS_Array_Assign (Right_Opnd (N));
         end if;
      else
         if Nkind (Left_Opnd (N)) = N_Op_Concat then
            return Do_RHS_Array_Assign (Left_Opnd (N))
              & (1 => Do_Expression (Right_Opnd (N)));
         else
            return (Do_Expression (Left_Opnd (N)),
                    Do_Expression (Right_Opnd (N)));
         end if;
      end if;
   end Do_RHS_Array_Assign;

   function Do_Array_Concatination (N : Node_Id) return Irep is
      --  Eventually concatination should be handled by a ggoto function
      --  similar to that used for an aggregate.
      --  For now to provide error recovery just return a string literal?
      Dummy   : constant String := "unsupported";
      Recover : constant Irep :=
        Make_String_Constant_Expr
          (Source_Location => Get_Source_Location (N),
           I_Type => Make_String_Type,
           Value => Dummy);
   begin
      Report_Unhandled_Node_Empty
        (N        => N,
         Fun_Name => "Do_Array_Concatination",
         Message  => "Array concatitination operator currenly unsupported");
      return Recover;
   end Do_Array_Concatination;

   function Do_Array_First_Last_Length (N : Node_Id; Attr : Attribute_Id)
                                        return Irep
   is
      The_Prefix  : constant Node_Id := Prefix (N);
      Attr_Expr   : constant Node_Id := First (Expressions (N));
      Dimension   : constant Pos :=
        (if Present (Attr_Expr) then
         --  Ada rules require the dimension expression to be static.
            UI_To_Int (Intval (Attr_Expr))
         else
         --  No dimension expression defaults to dimension 1
            1);
      Bounds      : constant Dimension_Bounds :=
        Do_Array_First_Last (The_Prefix, Dimension);
   begin
      return
        (case Attr is
            when Attribute_First => Bounds.Low,
            when Attribute_Last => Bounds.High,
            when others =>
               Calculate_Dimension_Length
           ("Do_Array_First_Last_Length -1", Bounds));
   end Do_Array_First_Last_Length;

   function Do_Array_First_Last (N : Node_Id;
                                 Dimension : Pos)
                                 return Dimension_Bounds
   is
      Dim_Index : Node_Id := First_Index (Etype (N));
   begin
      --  Get the right index for the dimension
      for I in 2 .. Dimension loop
         Dim_Index := Next_Index (Dim_Index);
      end loop;

      --  Now get the lower and upper bounds of the dimension
      Put_Line ("About to call Get_Dimension_Bounds");
      Print_Node_Briefly (N);

      declare
         Dim_Index_Type   : constant Entity_Id :=
           Etype (Get_Dimension_Index (N, Dimension));
         Index_I_Type     : constant Irep :=
           Make_Resolved_I_Type (Dim_Index_Type);
         Bounds : constant Dimension_Bounds :=
           Get_Dimension_Bounds (N, Dimension, Dim_Index);

         First  : constant Irep := Typecast_If_Necessary
           (Expr           => Bounds.Low,
            New_Type       => Index_I_Type,
            A_Symbol_Table => Global_Symbol_Table);
         Last   : constant Irep := Typecast_If_Necessary
           (Expr           => Bounds.High,
            New_Type       => Index_I_Type,
            A_Symbol_Table => Global_Symbol_Table);
      begin
         return (First, Last);
      end;
   end Do_Array_First_Last;

   -------------------------
   -- Get_Dimension_Index --
   -------------------------

   function Get_Dimension_Index (The_Array : Node_Id; Dim : Pos)
                                 return Node_Id
   is
      Dim_Iter : Node_Id := First_Index (Underlying_Type (Etype (The_Array)));
   begin
      for I in 2 .. Dim loop
         Dim_Iter := Next_Index (Dim_Iter);
      end loop;
      return Dim_Iter;
   end Get_Dimension_Index;

   -----------------------------------
   -- Make_Array_Object_From_Bounds --
   -----------------------------------

--     procedure Make_Array_Object_From_Bounds (Block          : Irep;
--                                              Array_Name     : String;
--                                              Target_Type    : Entity_Id;
--                                              Array_Length   : Irep;
--                                          Array_Bounds   : Dimension_Bounds;
--                                              Needs_Size_Var : Boolean;
--                                              Source_Loc     : Irep;
--                                              The_Array      : out Irep)
--     is
--        pragma Assert (Print_Msg ("Make_Array_Object_From_Bounds"));
--        Array_Id        : constant Symbol_Id := Intern (Array_Name);
--        Comp_Etype      : constant Entity_Id :=
--          Component_Type (Target_Type);
--        Comp_Type       : constant Irep :=
--          Make_Resolved_I_Type (Comp_Etype);
--
--        Array_Size_Var  : constant Irep :=
--          (if Needs_Size_Var then
--              Make_Symbol_Expr
--             (Source_Location => Source_Loc,
--              I_Type          => Index_T,
--              Range_Check     => False,
--              Identifier      => Array_Name & "_$array_size")
--           else
--              Ireps.Empty);
--        Array_Type_Irep  : constant Irep :=
--          Make_Array_Type
--            (I_Subtype => Comp_Type,
--             Size      =>
--               (if Needs_Size_Var then
--                   Array_Size_Var
--                else
--                   Array_Length));
--        Array_Sym_Irep   : constant Irep :=
--          Make_Symbol_Expr
--            (Source_Location => Source_Loc,
--             Identifier => Array_Name,
--             I_Type => Array_Type_Irep);
--        Decl             : constant Irep :=
--          Make_Code_Decl
--            (Symbol          => Array_Sym_Irep,
--             Source_Location => Source_Loc);
--        Array_Model_Size : constant Irep :=
--          Make_Op_Mul
--            (Rhs             => Typecast_If_Necessary
--               (Expr           =>
--                      ASVAT.Size_Model.Computed_Size (Comp_Etype),
--                New_Type       => Index_T,
--                A_Symbol_Table => Global_Symbol_Table),
--             Lhs             => Array_Length,
--             Source_Location => Source_Loc,
--             Overflow_Check  => False,
--             I_Type          => Index_T,
--             Range_Check     => False);
--     begin
--          --  The_Array symbol can be updeated with a constrained
--          --  length and the correct I_Array_Type.
--        The_Array := Array_Sym_Irep;
--
--        if not Global_Symbol_Table.Contains (Array_Id) then
--           --  Declare the array companion variables and the array object
--
--           Declare_First_Last_From_Bounds
--             (Prefix     => Array_Name,
--              Dimension  => "1",
--              Index_Type =>
--                Do_Type_Reference (Etype (First_Index (Target_Type))),
--              Bounds     => Array_Bounds,
--              Block      => Block);
--
--           Append_Op (Block, Decl);
--
--           New_Object_Symbol_Entry
--             (Object_Name       => Array_Id,
--              Object_Type       => Array_Type_Irep,
--              Object_Init_Value => Ireps.Empty,
--              A_Symbol_Table    => Global_Symbol_Table);
--           --  The model size of the object hast to be recorded.
--           ASVAT.Size_Model.Set_Computed_Size
--             (Id        => Array_Id,
--              Size_Expr => Array_Model_Size);
--        end if;
--     end Make_Array_Object_From_Bounds;

   ------------------------------------------------
   -- Make_Constrained_Array_From_Initialization --
   ------------------------------------------------
   procedure Make_Constrained_Array_From_Initialization
     (Block        : Irep;
      Array_Name   : String;
      Init_Expr    : Node_Id;
      The_Array    : out Irep;
      Array_Bounds : out Static_And_Dynamic_Bounds)
   is
      Expr_Kind    : constant Node_Kind := Nkind (Init_Expr);
      Source_Loc   : constant Irep := Get_Source_Location (Init_Expr);
      Expr_Type    : constant Entity_Id := Etype (Init_Expr);

      function Obtain_Bounds return Static_And_Dynamic_Bounds;
      function Obtain_Bounds return Static_And_Dynamic_Bounds is
      begin
         if Expr_Kind = N_Op_Concat then
            --  The array is initialized by a concatination.
            --  Determine the length of the concatination
            --  The resultant array from a concatination is 1 dimensional
            declare
               Cat_Array_Length : constant Irep :=
                 Calculate_Concat_Length (Init_Expr);
            begin
               --  Goto arrays start from zero.
               return Static_And_Dynamic_Bounds'
                 (Is_Unconstrained  => False,
                  Has_Static_Bounds => False,
                  Low_Static        => 0,
                  High_Static       => 0,
                  Low_Dynamic       => Index_T_Zero,
                  High_Dynamic      => Make_Op_Sub
                    (Rhs             => Index_T_One,
                     Lhs             => Cat_Array_Length,
                     Source_Location => Source_Loc,
                     I_Type          => Index_T));
            end;
         else
            return Multi_Dimension_Flat_Bounds ("500", Init_Expr);
         end if;
      end Obtain_Bounds;

      Bounds       : constant Static_And_Dynamic_Bounds := Obtain_Bounds;
   begin
      Put_Line ("Make_Constrained_Array_From_Initialization");
      Print_Node_Briefly (Init_Expr);
      Print_Node_Briefly (Expr_Type);
      if Expr_Kind = N_Op_Concat then
         Put_Line ("A concatination");
      end if;

      if Expr_Kind = N_Op_Concat or else Is_Constrained (Expr_Type) or else
        Is_Constr_Subt_For_U_Nominal (Expr_Type)
      then
         Put_Line ("Make_Constrained_Array_From_Initialization");
         --  Add the array object to the symbol table and declare it.
--           Array_Object_And_Friends
--                   (Array_Name   => Array_Name,
--                    The_Array    => The_Array,
--                    Array_Bounds => Bounds,
--                    Array_Node   => Init_Expr,
--                    Source_Loc   => Source_Loc,
--                    Block        => Block);

--        Put_Line ("Make_Constrained_Array_From_Initialization -The array");
--           Print_Irep (The_Array);
--           Print_Irep (Bounds.Low_Dynamic);
--           Print_Irep (Bounds.High_Dynamic);
         null;

      else
         Report_Unhandled_Node_Empty
           (Init_Expr,
            "Make_Constrained_Array_From_Initialization",
            "Unsupported unconstrained array initialization by " &
              Node_Kind'Image (Nkind (Init_Expr)));
         --  For to allow coninuation of translation an unconstrained object
         --  is declared.
         Array_Object_And_Friends
           (Array_Name   => Array_Name,
            Array_Node   => Init_Expr,
            The_Array    => The_Array,
            Array_Bounds => Bounds,
            Source_Loc   => Source_Loc,
            Block        => Block);
      end if;
      Array_Bounds := Bounds;
   end Make_Constrained_Array_From_Initialization;

   --------------
   -- Do_Slice --
   --------------

   --  A slice overlays an existing array.
   --  Do_Slice just returns the Irep of the existing, overlaid array and
   --  the restricted bounds of the slice are handled, where necessary in
   --  the subprograms which handle the use of slices.
--     --  The following comments are out of date and to be removed.
--     --  The following build an expression representing slice
--     --  orig(start .. end)
--     --  Let ArrT := struct { int first; int last; T* data; }
-- ----------------------------------------------------------------------------
--     --  ArrT slice_expr(ArrT orig) {
--     --    T* new_data = data + (start - orig.first);
--     --    ArrT temp_array = {.first=start, .last=end, .data=new_data};
--     --    return temp_array;
--     --  }
   ----------------------------------------------------------------------------
   function Do_Slice (N : Node_Id) return Irep is
      Source_Loc : constant Irep := Get_Source_Location (N);

      The_Prefix        : constant Node_Id := Prefix (N);
      Prefix_Etype      : constant Node_Id := Etype (The_Prefix);
      Is_Implicit_Deref : constant Boolean := Is_Access_Type (Prefix_Etype);
      Prefix_Irep       : constant Irep := Do_Expression (The_Prefix);
      --  The prefix to the slice may be an access to an array object
      --  which must be implicitly dereferenced.
      --  The base array from which the slice is taken.
      Base_Array_Type   : constant Node_Id :=
        (if Is_Implicit_Deref then
            Designated_Type (Prefix_Etype)
         else
            Prefix_Etype);
      Base_Type_Irep    : constant Irep :=
        Do_Type_Reference (Base_Array_Type);
--        Base_Comp_Type    : constant Irep :=
--          Do_Type_Reference (Component_Type (Base_Array_Type));
      Base_Irep         : constant Irep :=
        (if Is_Implicit_Deref then
            Make_Dereference_Expr
           (I_Type => Base_Type_Irep,
            Object => Prefix_Irep,
            Source_Location => Source_Loc)
         else
            Prefix_Irep);

      --  Any required implicit dereferencing has now been done.

--        --  Obtain the range of the slice from the constrained array subtype
--        --  added the ATree by the font-end.
--        Slice_Range       : constant Node_Id :=
--          Scalar_Range
--            (Etype (First_Index (Etype (N))));

--        --  Get the low and high bounds of the slice as Irep expressions.
--        --  They may be variable but the slice is always constrained.
--        Slice_First       : constant Irep :=
--          Do_Expression (Low_Bound (Slice_Range));
--        Slice_Last        : constant Irep :=
--          Do_Expression (High_Bound (Slice_Range));
--
--        pragma Assert (Print_Irep_Func (Slice_First));
--        pragma Assert (Print_Irep_Func (Slice_Last));
--
--        --  Now get the low and high bounds of the base array from which
--        --  the slice is taken.
--        --  The Irep expressions may be variable but the base array is
--        --  always constrained.
--        Base_First        : constant Irep :=
--          Do_Expression (Low_Bound (First_Index (Base_Array_Type)));
--        Base_Last         : constant Irep :=
--          Do_Expression (High_Bound (First_Index (Base_Array_Type)));
--
--        pragma Assert (Print_Irep_Func (Base_First));
--        pragma Assert (Print_Irep_Func (Base_Last));
--
--        --  Calculate the off set from the first element of the base array
--        --  to the first element of the slice.  The resulting index is
--        --  the first element of the slice.
--        Slice_Offset : constant Irep :=
--             Make_Op_Sub (Rhs             => Base_First,
--                          Lhs             => Slice_First,
--                          Source_Location => Source_Loc,
--                          Overflow_Check  => False,
--                          I_Type          => Int32_T);
--
--        pragma Assert (Print_Irep_Func (Slice_Offset));
--
--        --  Now index the first element of the slice from the base array.
--        Slice_Index : constant Irep :=
--          Make_Index_Expr
--               (I_Array         => Base_Irep,
--                Index           => Slice_Offset,
--                Source_Location => Source_Loc,
--                I_Type          => Base_Comp_Type,
--                Range_Check     => False);
--
--        pragma Assert (Print_Irep_Func (Slice_Index));
--
--        --  Obtain the address of the first element of the slice as
--        --  this is the address of the start of the slice
--        Slice_Addr : constant Irep :=
--          Make_Address_Of (Slice_Index);
--
--        pragma Assert (Print_Irep_Func (Slice_Addr));
--
--        --  Now convert this address to an array representation of the slice.
--        Slice_Array : constant Irep :=
--          Make_Op_Typecast
--            (Op0             => Slice_Index,
--             Source_Location => Source_Loc,
--             I_Type          =>
--               Make_Array_Type
--                 (I_Subtype => Base_Comp_Type,
--                  Size      => Calculate_Dimension_Length
--                    ((Slice_First, Slice_Last))),
--             Range_Check     => False);
--
--        pragma Assert (Print_Irep_Func (Slice_Array));

--        Slice_Params : constant Irep := Make_Parameter_List;
--        Slice_Args : constant Irep := Make_Argument_List;
--        Function_Name : constant String := "slice_expr";
--        Array_Param : constant Irep :=
--          Create_Fun_Parameter (Fun_Name        => Function_Name,
--                                Param_Name      => "orig_array",
--                                Param_Type      => Result_Type,
--                                Param_List      => Slice_Params,
--                                A_Symbol_Table  => Global_Symbol_Table,
--                                Source_Location => Source_Loc);
--
--        function Build_Slice_Func_Body return Irep;
--
--        function Build_Slice_Func_Body return Irep is
--           pragma Assert (Print_Mess ("Build_Slice_Func_Body Start"));
--           Base : constant Irep := Param_Symbol (Array_Param);
--           Idx_Type : constant Entity_Id :=
--             Etype (First_Index (Etype (N)));
--           New_First_Expr : constant Irep :=
--             Typecast_If_Necessary (Do_Expression (Low_Bound (Scalar_Range
--                                    (Idx_Type))), CProver_Size_T,
--                                    Global_Symbol_Table);
--           Old_First_Expr : constant Irep :=
--             Make_Member_Expr (Compound         => Base,
--                               Source_Location  => Source_Loc,
--                               Component_Number => 0,
--                               I_Type           => CProver_Size_T,
--                               Component_Name   => "first1");
--
--           New_Last_Expr : constant Irep :=
--             Typecast_If_Necessary (Do_Expression (High_Bound (Scalar_Range
--                                    (Idx_Type))), CProver_Size_T,
--                                    Global_Symbol_Table);
--           Result_Block : constant Irep :=
--             Make_Code_Block (Source_Loc, CProver_Nil_T);
--           Array_Temp : constant Irep :=
--             Fresh_Var_Symbol_Expr (Result_Type, "temp_array");
--
--           Offset : constant Irep :=
--             Make_Op_Sub (Rhs             => Old_First_Expr,
--                          Lhs             => New_First_Expr,
--                          Source_Location => Source_Loc,
--                          Overflow_Check  => False,
--                          I_Type          => CProver_Size_T);
--           pragma Assert (Print_Mess ("Build_Slice_Func_Body  .."));
--           New_Data : constant Irep :=
--             Offset_Array_Data (Base         => Base,
--                                Offset       => Offset);
--           pragma Assert (Print_Mess ("Build_Slice_Func_Body_Done"));
--           Result : constant Irep :=
--             Make_Struct_Expr (Source_Location => Source_Loc,
--                               I_Type          => Result_Type);
--
--           Data_Temp : constant Irep :=
--             Fresh_Var_Symbol_Expr (Get_Type (New_Data), "temp_array_data");
--        begin
--           Append_Struct_Member (Result, New_First_Expr);
--           Append_Struct_Member (Result, New_Last_Expr);
--           Append_Struct_Member (Result, Data_Temp);
--
--           Append_Op (Result_Block,
--                      Make_Code_Assign (Rhs             => New_Data,
--                                        Lhs             => Data_Temp,
--                                        Source_Location => Source_Loc));
--           Append_Op (Result_Block,
--                      Make_Code_Assign (Rhs             => Result,
--                                        Lhs             => Array_Temp,
--                                        Source_Location => Source_Loc));
--
--           Append_Op (Result_Block,
--                      Make_Code_Return (Return_Value    => Array_Temp,
--                                        Source_Location => Source_Loc));
--           return Result_Block;
--        end Build_Slice_Func_Body;
--
--        Func_Symbol : constant Symbol :=
--          Build_Function (Name           => Function_Name,
--                          RType          => Result_Type,
--                          Func_Params    => Slice_Params,
--                          FBody          => Build_Slice_Func_Body,
--                          A_Symbol_Table => Global_Symbol_Table);
--        Slice_Id : constant Irep := Base_Irep;
   begin
      return Base_Irep;
--        return Slice_Array;
--        return Make_Side_Effect_Expr_Function_Call (
--                                   Arguments       => Slice_Args,
--                              I_Function      => Symbol_Expr (Func_Symbol),
--                                   Source_Location => Source_Loc,
--                                   I_Type          => Result_Type);
   end Do_Slice;

   --------------------------
   -- Do_Indexed_Component --
   --------------------------

   function Do_Indexed_Component (N : Node_Id) return Irep is
      pragma Assert (Print_Msg ("Do_Indexed_Component "));
      pragma Assert (Print_Node (N));
      pragma Assert (Print_Node (Prefix (N)));

      Source_Loc        : constant Irep := Get_Source_Location (N);
      Pre_Prefix        : constant Node_Id := Prefix (N);
      --  The prefix may be a slice.  The underlying array needs to be
      --  indexed and not the slice.
      The_Prefix        : constant Node_Id :=
        (if Nkind (Pre_Prefix) = N_Slice then
              Get_Underlying_Array_From_Slice (Pre_Prefix)
         else
            Pre_Prefix);
      Prefix_Etype      : constant Node_Id := Etype (The_Prefix);
      --  The prefix to an indexed component may be an access to an
      --  array object which must be implicitly dereferenced.
      Is_Implicit_Deref : constant Boolean := Is_Access_Type (Prefix_Etype);

      Array_Type : constant Entity_Id :=
        (if Is_Implicit_Deref then
            Designated_Type (Prefix_Etype)
         else
            Prefix_Etype);

      Prefix_Irep       : constant Irep := Do_Expression (The_Prefix);
      Resolved_Type     : constant Irep := Do_Type_Reference (Array_Type);

      Base_Irep         : constant Irep :=
        (if Is_Implicit_Deref then
            Make_Dereference_Expr
           (I_Type => Resolved_Type,
            Object => Prefix_Irep,
            Source_Location => Get_Source_Location (N))
         else
            Prefix_Irep);

--        Base_I_Type       : constant Irep := Get_Type (Base_Irep);
--        pragma Assert (Kind (Base_I_Type) in I_Array_Type | I_Pointer_Type);
--
      Element_Type : constant Irep :=
        Do_Type_Reference (Component_Type (Array_Type));

      Index        : constant Irep := Typecast_If_Necessary
        (Expr           => Calculate_Index_Offset
           (Array_Node  => The_Prefix,
            Array_Type  => Array_Type,
            The_Indices => N),
         New_Type       => Index_T,
         A_Symbol_Table => Global_Symbol_Table);

      Indexed_Data : constant Irep :=
        Make_Resolved_Index_Expr (The_Array  => Base_Irep,
                                  Zero_Index => Index,
                                  I_Type     => Element_Type,
                                  Location   => Source_Loc);
   begin
      Put_Line ("Do_Indexed_Component");
      Print_Irep (Base_Irep);
      Print_Irep (Indexed_Data);
      return
        Indexed_Data;
   end Do_Indexed_Component;

   -------------------------
   -- Get_Array_Reference --
   -------------------------

   function Get_Array_Reference (Array_Irep : Irep; Component_Irep : Irep)
                                 return Irep is
     (Get_Pointer_To_Array (Array_Irep, Component_Irep));

   ----------------------------------
   -- Get_Non_Array_Component_Type --
   ----------------------------------

   function Get_Non_Array_Component_Type (A : Entity_Id) return Entity_Id is
      This_Subtype : Entity_Id := Component_Type (A);
   begin
      while Is_Array_Type (This_Subtype) loop
         This_Subtype := Component_Type (This_Subtype);
      end loop;
      return This_Subtype;
   end Get_Non_Array_Component_Type;

   function Get_Underlying_Array_From_Slice (N : Node_Id) return Node_Id is
      Result : Node_Id := N;
   begin
      while Nkind (Result) = N_Slice loop
         Result := Prefix (Result);
      end loop;
      return Result;
   end Get_Underlying_Array_From_Slice;

   function Make_Constrained_Array_Subtype (Declaration : Node_Id)
       return Irep
   is
      Source_Location : constant Irep := Get_Source_Location (Declaration);
      Array_Entity    : constant Entity_Id :=
        (if Nkind (Declaration) = N_Defining_Identifier then
              Declaration
         else
            Defining_Identifier (Declaration));
      Comp_Type      : constant Entity_Id := Component_Type (Array_Entity);
      Comp_Irep      : constant Irep :=
        Make_Resolved_I_Type (Comp_Type);
      --  Get the array zero based bounds.
      --  If the array is multi-dimmensional, the bounds are calculated
      --  by flattening th array into a one-dimensional eaquivalent.
      --  ASVAT represents multimensional arrays as equivalent one
      --  dimensional arrays.
      --  All goto arrays are index from 0, so the length is
      --  upper bound + 1.
      Array_Bounds     : constant Static_And_Dynamic_Bounds :=
        Multi_Dimension_Flat_Bounds ("8", Array_Entity);
      pragma Assert (Print_Msg ("Return from Multi_Dimension_Flat_Bounds 8"));
      pragma Assert (Print_Msg ("Array bounds unconstrained " &
                       Boolean'Image (Array_Bounds.Is_Unconstrained)));
      pragma Assert (Print_Msg ("Array bounds static " &
                       Boolean'Image (Array_Bounds.Has_Static_Bounds)));
      pragma Assert (Print_Msg ("Array bounds static low " &
                       Int'Image (Array_Bounds.Low_Static)));
      pragma Assert (Print_Msg ("Array bounds static High " &
                       Int'Image (Array_Bounds.High_Static)));
      pragma Assert (Print_Irep_Func (Array_Bounds.Low_Dynamic));
      pragma Assert (Print_Irep_Func (Array_Bounds.High_Dynamic));

      Array_Length     : constant Irep :=
        (if Array_Bounds.Has_Static_Bounds then
            Integer_Constant_To_Expr
           (Value           => UI_From_Int (Array_Bounds.High_Static + 1),
            Expr_Type       => Index_T,
            Source_Location => Source_Location)
         else
            Make_Op_Add
           (Rhs             => Index_T_One,
            Lhs             => Array_Bounds.High_Dynamic,
            Source_Location => Source_Location,
            Overflow_Check  => False,
            I_Type          => Index_T,
            Range_Check     => False));

      pragma Assert
        (if not ASVAT.Size_Model.Has_Size (Comp_Type) then
             (Print_Msg ("The missing size is:") and Print_Node (Comp_Type))
         else
             True);

      Array_Model_Size : constant Irep :=
        Make_Op_Mul
          (Rhs             => Typecast_If_Necessary
             (Expr           =>
                    ASVAT.Size_Model.Computed_Size (Comp_Type),
              New_Type       => Index_T,
              A_Symbol_Table => Global_Symbol_Table),
           Lhs             => Array_Length,
           Source_Location => Source_Location,
           Overflow_Check  => False,
           I_Type          => Index_T,
           Range_Check     => False);
   begin
      Put_Line ("Make_Constrained_Array_Subtype");
      --  Set the ASVAT.Size_Model size for the array.
      ASVAT.Size_Model.Set_Computed_Size
        (Array_Entity, Array_Model_Size);
      if not Array_Bounds.Has_Static_Bounds then
         --  The array has at least one dimension which has an
         --  Ada variable specifying a bound.
         --  A variable rather than an expression must be used to define the
         --  length of the goto array.
         declare
            Array_Name   : constant String := Unique_Name (Array_Entity);
            Arr_Len      : constant String := Array_Name & "_$array_size";
            Arr_Len_Id   : constant Symbol_Id := Intern (Arr_Len);
            Arr_Len_Irep : constant Irep :=
              Make_Symbol_Expr
                (Source_Location => Source_Location,
                 I_Type          => Index_T,
                 Range_Check     => False,
                 Identifier      => Arr_Len);
         begin
            --  If the array subtype is an Itype then there is no point
            --  declaring the variable in the goto code as the type
            --  declaration is anonymous and does not appear in the
            --  goto code.
            --  Add the new variable to the symbol table and set its value
            --  to the computed length.
            New_Object_Symbol_Entry
              (Object_Name       => Arr_Len_Id,
               Object_Type       => Index_T,
               Object_Init_Value => Array_Length,
               A_Symbol_Table    => Global_Symbol_Table);

            --  Return the dynamic array type
            --  using the declared array length variable.
            Put_Line ("Make_Constrained_Array_Subtype - return dynamic");
            return Make_Array_Type
              (I_Subtype => Comp_Irep,
               Size      => Arr_Len_Irep);
         end;
      end if;
      --  Return the array type using the static
      --  length of the array.
      Put_Line ("Make_Constrained_Array_Subtype - return static");
      return Make_Array_Type
        (I_Subtype => Comp_Irep,
         Size      => Array_Length);
   end Make_Constrained_Array_Subtype;

   function Make_Unconstrained_Array_Subtype (Declaration    : Node_Id;
                                              Component_Type : Entity_Id)
                                              return Irep
   is
      pragma Assert (Print_Msg ("Make_Unconstrained_Array_Subtype"));
      Array_Type : constant Entity_Id := Defining_Identifier (Declaration);
      Sub : constant Irep :=
        Make_Resolved_I_Type (Component_Type);
      Dimensions  : constant Pos := Number_Dimensions (Array_Type);

      pragma Assert (Print_Irep_Func (Sub));
      --  An unconstrained array type is representad as an array_struc type
      Array_Struc : constant Irep := Make_Array_Struc_Type
        (Comp_Type  => Sub,
         Location   => Get_Source_Location (Declaration),
         Dimensions => Dimensions);

      pragma Assert (Print_Irep_Func (Array_Struc));
   begin
      Put_Line ("About to set the size");
      --  Set the ASVAT.Size_Model size for the unconstrained array to
      --  the size of the array structure.
      ASVAT.Size_Model.Set_Static_Size
        (Array_Type, Integer (Get_Array_Struc_Type_Size (Dimensions)));
      Put_Line ("Size set");
      return Array_Struc;
   end Make_Unconstrained_Array_Subtype;

   procedure Build_Unconstrained_Array_Result  (Block       : Irep;
                                                Result_Var  : Irep;
                                                Return_Expr : Node_Id)
   is
      Source_Loc   : constant Irep := Get_Source_Location (Return_Expr);
      Array_Type   : constant Entity_Id :=
        Underlying_Type (Etype (Return_Expr));
      N_Dimensions : constant Pos := Number_Dimensions (Array_Type);
      Comp_Type    : constant Entity_Id := Component_Type (Array_Type);
   begin
      Put_Line ("Build_Unconstrained_Array_Result");
      Declare_Itype (Array_Type);
      --  Some of the following declarations must occur after the
      --  call to Declare_Itype as the array type may be an Itype and
      --  its details need to be recorded in the symbol table.
      --  For instance, Do_Type_Reference requires the Irep type information
      --  for the Array type to be in the global symbol table.
      declare
         Comp_I_Type  : constant Irep :=
           Make_Resolved_I_Type (Comp_Type);

         Source_I_Type : constant Irep :=
           Do_Type_Reference (Array_Type);
         Arr_Ptr_Type  : constant Irep := Make_Pointer_Type (Comp_I_Type);

         --  This array of the first and last of each dimension
         --  must have a lower bound of zero.
         Array_Dim_Bounds : Bounds_Array (0 .. (2 * N_Dimensions - 1));

         Array_Bounds     : constant Static_And_Dynamic_Bounds :=
           Multi_Dimension_Flat_Bounds ("32", Array_Type);
         Array_Size       : constant Irep := Typecast_If_Necessary
           (Expr           => ASVAT.Size_Model.Make_Byte_Aligned_Size
              (ASVAT.Size_Model.Computed_Size (Array_Type)),
            New_Type       => Index_T,
            A_Symbol_Table => Global_Symbol_Table);

         --   Allocate an array to hold the funtion result.
         Malloc_Args  : constant Irep := Make_Argument_List;
         Malloc_Name  : constant String := "malloc";
         Malloc_Call  : constant Irep :=
           Make_Side_Effect_Expr_Function_Call
             (Arguments       => Malloc_Args,
              I_Function      => Symbol_Expr
                (Global_Symbol_Table (Intern (Malloc_Name))),
              Source_Location => Source_Loc,
              I_Type          => Make_Pointer_Type (Make_Void_Type));
         Array_Malloc : constant Irep :=
           Typecast_If_Necessary
             (Expr           => Malloc_Call,
              New_Type       => Arr_Ptr_Type,
              A_Symbol_Table => Global_Symbol_Table);

         --  A variable to point to the allocated array.
         Array_Ref    : constant Irep :=
           Fresh_Var_Symbol_Expr (Arr_Ptr_Type, "array_ref");

         --  A variable to hold the array result so that the array is
         --  only called once.
         Fun_Result   : constant Irep :=
           Fresh_Var_Symbol_Expr (Source_I_Type, "fun_result");

         Index : Node_Id := First_Index (Array_Type);
      begin
         --  Fill the bounds array.
         for I in 1 .. N_Dimensions loop
            declare
               Dim_Bounds  : constant Dimension_Bounds :=
                 Get_Dimension_Bounds (Array_Type, I, Index);
            begin
               Put_Line ("Build_Unconstrained_Array_Result - fill bounds");
               Print_Irep (Get_Op0 (Dim_Bounds.Low));
               Print_Irep (Get_Op0 (Dim_Bounds.High));
               --  Assign the first value for this dimension.
               Array_Dim_Bounds (I * 2 - 2) :=
                 Typecast_If_Necessary
                   (Expr           => Dim_Bounds.Low,
                    New_Type       => Bounds_Component,
                    A_Symbol_Table => Global_Symbol_Table);
               --  Now the last value for this dimension.
               Array_Dim_Bounds (I * 2 - 1) :=
                Typecast_If_Necessary
                   (Expr           => Dim_Bounds.High,
                    New_Type       => Bounds_Component,
                    A_Symbol_Table => Global_Symbol_Table);
            end;
            Index := Next_Index (Index);
         end loop;

         --  Now create the malloced array to hold the result.
         Append_Argument (Malloc_Args, Array_Size);

         Append_Declare_And_Init
           (Symbol     => Array_Ref,
            Value      => Array_Malloc,
            Block      => Block,
            Source_Loc => Source_Loc);

         Append_Declare_And_Init
           (Symbol     => Fun_Result,
            Value      => Typecast_If_Necessary
              (Expr           => Do_Expression (Return_Expr),
               New_Type       => Get_Type (Fun_Result),
               A_Symbol_Table => Global_Symbol_Table),
            Block      => Block,
            Source_Loc => Source_Loc);

         Put_Line ("Copying array");
         --  Now copy the return expression to the allocated array.
         Print_Irep (Fun_Result);
         Print_Irep (Source_I_Type);
         Print_Irep (Get_Type (Fun_Result));
         Copy_Array
           (Block         => Block,
            Dest_Bounds   => Array_Bounds,
            Source_Bounds => Array_Bounds,
            Dest_Irep     => Array_Ref,
            Source_Irep   => Get_Pointer_To_Array (Fun_Result, Comp_I_Type));
         Print_Irep (Array_Ref);

         Put_Line ("Initialising the result Array_Struc");
         --  Initialise the result Array_Struc
         Init_Array_Struc
           (Block       => Block,
            Array_Struc => Result_Var,
            Array_Ptr   => Array_Ref,
            Location    => Source_Loc,
            Bounds      => Array_Dim_Bounds);
         Put_Line ("Result_Var");
         Print_Irep (Result_Var);
      end;
   end Build_Unconstrained_Array_Result;

   procedure Pass_Array_Friends (Actual_Array : Entity_Id;
                                 Array_Irep   : Irep;
                                 Args         : Irep) is
--        Array_Name   : constant String := Unique_Name (Actual_Array);
      Array_Type   : constant Entity_Id :=
        Underlying_Type (Etype (Actual_Array));

      Index_Iter   : Node_Id := First_Index (Array_Type);
   begin
      for Dimension in 1 .. Number_Dimensions (Array_Type) loop
         pragma Assert (Present (Index_Iter));
         declare
            Bounds : constant Dimension_Bounds :=
              (if Is_Unconstrained_Array_Result (Array_Irep) then
                    Get_Bounds_From_Struc (Array_Irep, Dimension)
               else
                  Do_Array_First_Last (Actual_Array, Dimension));
         begin
            Append_Argument (Args, Bounds.Low);
            Append_Argument (Args, Bounds.High);
         end;
         Index_Iter := Next_Index (Index_Iter);
      end loop;
   end Pass_Array_Friends;

   procedure Update_Array_From_Concatenation
           (Block       : Irep;
            Concat      : Node_Id;
            Dest_Bounds : Static_And_Dynamic_Bounds;
            Dest_Array  : Irep)
   is
      Source_Loc : constant Irep := Get_Source_Location (Concat);

      Accum_Index : Static_And_Dynamic_Index :=
        Static_And_Dynamic_Index'
          (Is_Static     => Dest_Bounds.Has_Static_Bounds,
           Static_Index  => UI_From_Int (Dest_Bounds.Low_Static),
           Dynamic_Index => Dest_Bounds.Low_Dynamic);

      procedure Process_Catenation (N : Node_Id);

      procedure Process_Catenation (N : Node_Id) is
      begin
         Put_Line ("Process_Catenation");
         Print_Node_Briefly (N);
         Put_Line ("Is static index " & Boolean'Image (Accum_Index.Is_Static));
         Put_Line (Int'Image (UI_To_Int (Accum_Index.Static_Index)));
         Print_Irep (Accum_Index.Dynamic_Index);
         if Nkind (N) = N_Op_Concat then
            if Is_Component_Left_Opnd (N) then
               Put_Line ("Left - a component");
               Print_Node_Briefly (Left_Opnd (N));
               Assign_To_Array_Component
                 (Block      => Block,
                  The_Array  => Dest_Array,
                  Zero_Index => Get_Dynamic_Index (Accum_Index),
                  Value_Expr => Do_Expression (Left_Opnd (N)),
                  I_Type     => Get_Subtype (Get_Type (Dest_Array)),
                  Location   => Source_Loc);
               Add_One_To_Index (Accum_Index);
            else
               Put_Line ("Left - not a component");
               Print_Node_Briefly (Left_Opnd (N));
               Process_Catenation
                 (N           => Left_Opnd (N));
            end if;
            if Is_Component_Right_Opnd (N) then
               Put_Line ("Right - a component");
               Print_Node_Briefly (Right_Opnd (N));
               Print_Irep (Dest_Array);
               Assign_To_Array_Component
                 (Block      => Block,
                  The_Array  => Dest_Array,
                  Zero_Index => Get_Dynamic_Index (Accum_Index),
                  Value_Expr => Do_Expression (Right_Opnd (N)),
                  I_Type     => Get_Subtype (Get_Type (Dest_Array)),
                  Location   => Source_Loc);
               Add_One_To_Index (Accum_Index);
            else
               Put_Line ("Right - not a component");
               Print_Node_Briefly (Right_Opnd (N));
               Process_Catenation
                 (N           => Right_Opnd (N));
            end if;
         else
            Put_Line ("Not a concat");
            declare
               --  In a concatenation the array can only have one dimension.
               Array_Entity : constant Node_Id :=
                 (if Nkind (N) in N_Entity then
                       N
                  elsif Nkind (N) in N_Has_Entity then
                       Entity (N)
                  elsif Nkind (N) in N_Has_Etype then
                       Etype (N)
                  else
                     Types.Empty);
--                 Array_Type      : constant Entity_Id :=
--                   Underlying_Type (Array_Entity);
               Array_Bounds    : constant Static_And_Dynamic_Bounds :=
                 Multi_Dimension_Flat_Bounds ("102", Array_Entity);
               Next_Length    : constant Static_And_Dynamic_Index :=
                 Get_Array_Size_From_Bounds (Array_Bounds);

               New_Index   : constant Static_And_Dynamic_Index :=
                 Add_To_Index (Accum_Index, Next_Length);

               High_Index  : constant Static_And_Dynamic_Index :=
                 Sub_One_From_Index (New_Index);

               Dest_Bounds : constant Static_And_Dynamic_Bounds :=
                 Static_And_Dynamic_Bounds'
                   (Is_Unconstrained  => False,
                    Has_Static_Bounds => Accum_Index.Is_Static,
                    Low_Static        => UI_To_Int (Accum_Index.Static_Index),
                    High_Static       => UI_To_Int (High_Index.Static_Index),
                    Low_Dynamic       => Accum_Index.Dynamic_Index,
                    High_Dynamic      => High_Index.Dynamic_Index);
            begin
               Put_Line ("Process_Catination - completing");
               Put_Line ("Isstatic " & Boolean'Image (Next_Length.Is_Static));
               Put_Line ("Static length " &
                           Int'Image (UI_To_Int (Next_Length.Static_Index)));
               Print_Irep (Next_Length.Dynamic_Index);
               if Kind (Next_Length.Dynamic_Index) = I_Op_Add then
                  Put_Line ("An op add");
                  Print_Irep (Get_Lhs (Next_Length.Dynamic_Index));
                  Print_Irep (Get_Rhs (Next_Length.Dynamic_Index));
               end if;

               Put_Line ("Dest_Bounds");
               Put_Line ("Has_Static Dest_Bounds " &
                           Boolean'Image (Dest_Bounds.Has_Static_Bounds));
               Put_Line ("Low static " &
                           Int'Image (Dest_Bounds.Low_Static));
               Put_Line ("High static " &
                           Int'Image (Dest_Bounds.High_Static));
               Print_Irep (Dest_Bounds.Low_Dynamic);
               Print_Irep (Dest_Bounds.High_Dynamic);
               if Kind (Dest_Bounds.Low_Dynamic) = I_Op_Add then
                  Print_Irep (Get_Lhs (Dest_Bounds.Low_Dynamic));
                  Print_Irep (Get_Rhs (Dest_Bounds.High_Dynamic));
               end if;

               Put_Line ("New_Index is static " &
                           Boolean'Image (New_Index.Is_Static));
               Put_Line ("New_Index " &
                           Int'Image (UI_To_Int (New_Index.Static_Index)));
               Print_Irep (New_Index.Dynamic_Index);
               if Kind (New_Index.Dynamic_Index) = I_Op_Add then
                  Print_Irep (Get_Lhs (New_Index.Dynamic_Index));
                  Print_Irep (Get_Rhs (New_Index.Dynamic_Index));
               end if;
               if not Array_Bounds.Is_Unconstrained then
                  Array_Assignment_Op
                    ("3",
                     Source_Expr  => N,
                     N_Dimensions => 1,
                     Dest_Bounds  => Dest_Bounds,
                     Target_Array => Dest_Array,
                     Block        => Block);
                  Accum_Index := New_Index;
               else
                  Report_Unhandled_Node_Empty
                    (N        => N,
                     Fun_Name => "Process_Catination",
                     Message  => "Unconstrained array expressions in " &
                       "concatinations are unsupported");
               end if;
            end;
         end if;
      end Process_Catenation;

   begin
      Put_Line ("Update_Array_From_Catination");
      Print_Irep (Dest_Bounds.Low_Dynamic);
      Print_Irep (Dest_Bounds.High_Dynamic);
      Process_Catenation (Concat);
   end Update_Array_From_Concatenation;

   procedure Update_Array_From_Slice
           (Block       : Irep;
            Slice       : Node_Id;
            Dest_Array  : Irep;
            Dest_Bounds : Static_And_Dynamic_Bounds)
   is
      --  Do expression of a slice returns the array from which the
      --  slice is taken.
      Underlying_Array : constant Irep := Do_Expression (Slice);

      --  Get the slice bounds which are represented as offsets from the
      --  start of the array upon which the slice is defined.
      Slice_Bounds : constant Static_And_Dynamic_Bounds :=
        Zero_Based_Bounds (Slice);
   begin
      --  A check that the source and destination arrays have the
      --  same length may be required.
      Check_Equal_Array_Lengths (Block, Slice_Bounds, Dest_Bounds);
      Copy_Array
        (Block         => Block,
         Dest_Bounds   => Dest_Bounds,
         Source_Bounds => Slice_Bounds,
         Dest_Irep     => Dest_Array,
         Source_Irep   => Underlying_Array);
   end Update_Array_From_Slice;

   procedure Update_Array_From_String_Literal
     (Block        : Irep;
      Str_Lit      : Node_Id;
      Dest_Array   : Irep)
   is
      Source_Location   : constant Irep := Get_Source_Location (Str_Lit);
      --  String literals are stored in string constants table described
      --  Stringst.
      --  Their lower bound is always 1 and therefore the string length
      --  is also the string litera['s high bound.
      Str_Id            : constant String_Id := Strval (Str_Lit);
      Str_Lit_Length     : constant Nat := String_Length (Str_Id);
      Str_Lit_Low       : constant Pos := 1;
      Component_Itype   : constant Irep :=
        Get_Subtype (Get_Type (Dest_Array));
   begin
      for I in Str_Lit_Low .. Str_Lit_Length loop
         Assign_To_Array_Component
              (Block      => Block,
               The_Array  => Dest_Array,
               Zero_Index =>
                 Integer_Constant_To_Expr
                   (Value           => UI_From_Int (I - 1),
                    Expr_Type       => Index_T,
                    Source_Location => Source_Location),
               Value_Expr => Integer_Constant_To_Expr
                 (Value           => UI_From_Int
                      (Nat (Get_String_Char (Str_Id, I))),
                  Expr_Type       => Component_Itype,
                  Source_Location => Source_Location),
               I_Type     => Component_Itype,
               Location   => Source_Location);
      end loop;
   end Update_Array_From_String_Literal;

end Arrays;
