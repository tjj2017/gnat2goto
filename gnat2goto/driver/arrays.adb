with Nlists;                use Nlists;
with Uintp;                 use Uintp;
with Namet;                 use Namet;
with Tree_Walk;             use Tree_Walk;
with Aggregates;            use Aggregates;
with Follow;                use Follow;
with Range_Check;           use Range_Check;
with ASVAT.Size_Model;
with Sem_Util;              use Sem_Util;
with Sem_Eval;              use Sem_Eval;
with Arrays.Low_Level;      use Arrays.Low_Level;
with Treepr;                use Treepr;
with Text_IO;               use Text_IO;
package body Arrays is
   function Defining_Identifier (N : Node_Id) return Entity_Id;
   function Defining_Identifier (N : Node_Id) return Entity_Id is
      NT : constant Node_Kind := Nkind (N);
   begin
      Put_Line ("Into Defining_Identifier");
      Print_Node_Briefly (N);
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
         Put_Line ("Illegal node to Defining_Identifier");
      end if;

      return Sinfo.Defining_Identifier (N);
   end Defining_Identifier;

   package Debug_Help is
      function Print_Node (N : Node_Id; Subtree : Boolean := False)
                           return Boolean;
      function Print_Irep_Func (I : Irep) return Boolean;
      function Print_Msg (Msg : String) return Boolean;
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

   procedure Array_Object_And_Friends (Array_Name : String;
                                       Array_Type : Entity_Id;
                                       Source_Loc : Irep;
                                       Block      : Irep)
   with Pre => Is_Array_Type (Array_Type);

   procedure Array_Assignment_Op (Source_Expr  : Node_Id;
                                  Dest_Node    : Node_Id;
                                  Dest_Bounds  : Static_And_Dynamic_Bounds;
                                  Target_Array : Irep;
                                  Block        : Irep)
   with Pre => Is_Array_Type (Etype (Source_Expr)) and
               Kind (Get_Type (Target_Array)) = I_Array_Type;

   procedure Declare_First_Last_From_Bounds (Prefix     : String;
                                             Dimension  : String;
                                             Index_Type : Entity_Id;
                                             Bounds     : Dimension_Bounds;
                                             Block      : Irep);
   --  This is similar to Declare_First_Last_Vars but is called at a slightly
   --  lower-level with the index node replaced by the Index_Type node and
   --  the dimension Bounds.

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

   function Do_Constrained_First_Last (E         : Entity_Id;
                                       Dimension : Positive)
                                       return Dimension_Bounds
     with Pre => Is_Array_Type (Etype (E)) and then
                 not Is_Formal (E);

   function Do_Unconstrained_First_Last (The_Array  : Entity_Id;
                                         Dimension  : Positive;
                                         Source_Loc : Irep)
                                         return Dimension_Bounds
     with Pre => Is_Array_Type (Etype (The_Array)) and not
     Is_Constrained (The_Array);

   procedure Make_Array_Object_From_Bounds (Block        : Irep;
                                            Array_Name   : String;
                                            Target_Type  : Entity_Id;
                                            Array_Length : Irep;
                                            Array_Bounds : Dimension_Bounds;
                                            Source_Loc   : Irep;
                                            The_Array    : out Irep)
     with Pre => (Is_Array_Type (Target_Type) and
                 not Is_Constrained (Target_Type)) and then
                 Number_Dimensions (Target_Type) = 1;
   --  Decalre a one-dimensional array from the given target type,
   --  its length and its bounds.
   --  Also declare the First and Last companion variables for the
   --  unconstrained array.

   procedure Make_Constrained_Array_From_Initialization
     (Block        : Irep;
      Target_Type  : Entity_Id;
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

   procedure Array_Assignment_Op (Source_Expr  : Node_Id;
                                  Dest_Node    : Node_Id;
                                  Dest_Bounds  : Static_And_Dynamic_Bounds;
                                  Target_Array : Irep;
                                  Block        : Irep)
   is
      pragma Assert (Print_Msg ("Into Array_Assignment_Op"));
      pragma Assert (Print_Node (Source_Expr));
      Source_Location  : constant Irep := Get_Source_Location (Source_Expr);
      pragma Assert (Print_Node (Dest_Node));
      Dest_Type        : constant Entity_Id := Etype (Dest_Node);

      RHS_Node_Kind    : constant Node_Kind := Nkind (Source_Expr);
      Source_Type      : constant Entity_Id := Etype (Source_Expr);
      pragma Assert (Print_Node (Source_Expr));
      pragma Assert (Print_Msg ("Array_Assignment_Op: about to call Multi"));

      Source_Bounds : constant Static_And_Dynamic_Bounds :=
        Multi_Dimension_Flat_Bounds (Source_Expr);
   begin
      Put_Line ("Do_Assignment_Op after initial declarations");
      if RHS_Node_Kind = N_Aggregate then
         Update_Array_From_Aggregate
           (Block        => Block,
            Agg          => Source_Expr,
            N_Dimensions => Number_Dimensions (Dest_Type),
            Dest_Bounds  => Dest_Bounds,
            Dest_Array   => Target_Array);
      elsif RHS_Node_Kind = N_Slice then
         Put_Line ("RHS is a slice");
         Print_Node_Briefly (Source_Expr);
         Update_Array_From_Slice
           (Block       => Block,
            Slice       => Source_Expr,
            Dest_Array  => Target_Array,
            Dest_Bounds => Dest_Bounds);
      elsif RHS_Node_Kind = N_Op_Concat then
         Put_Line ("Op Concat");
         Print_Node_Subtree (Source_Expr);
         Update_Array_From_Concatenation
           (Block       => Block,
            Concat      => Source_Expr,
            Dest_Array  => Target_Array,
            Dest_Bounds => Dest_Bounds);
      elsif RHS_Node_Kind = N_Function_Call then
         declare
            Func_Result_Type : constant Entity_Id := Etype (Source_Expr);
         begin
            Put_Line ("Function Call");
            Print_Node_Subtree (Source_Expr);
            Print_Irep (Do_Expression (Source_Expr));
            Print_Node_Subtree (First_Index (Func_Result_Type));
            if not Is_Constrained (Func_Result_Type) then
               Report_Unhandled_Node_Empty
                 (N        => Source_Expr,
                  Fun_Name => "Array_Assignment_Op",
                  Message  => "A function call returning an unconstrained "
                  & "array type is unsupported");
            elsif not All_Dimensions_Static (Func_Result_Type) then
               Report_Unhandled_Node_Empty
                 (N        => Source_Expr,
                  Fun_Name => "Array_Assignment_Op",
                  Message  => "A function call returning an array with "
                  & "non-static bounds is unsupported");
            end if;
         end;
      elsif not Dest_Bounds.Is_Unconstrained then
         if Dest_Bounds.Has_Static_Bounds and
           Source_Bounds.Has_Static_Bounds
         then
            --  Both source and destination have static bounds.
            --   A simple assignment should work.
            Put_Line ("Simple assignment");
            Print_Irep (Target_Array);
            Print_Irep (Get_Type (Target_Array));
            Print_Irep (Get_Subtype (Get_Type (Target_Array)));
            Print_Irep (Do_Expression (Source_Expr));
            Print_Irep
              (Get_Type (Do_Expression (Source_Expr)));
            Print_Irep
              (Get_Subtype (Get_Type (Do_Expression (Source_Expr))));
            declare
               Source_Irep  : constant Irep :=
                 Do_Expression (Source_Expr);
               Target_Itype : constant Irep :=
                 Get_Type (Target_Array);
               Source_Itype : constant Irep :=
                 (if Is_Constrained (Etype (Source_Expr)) then
                     Get_Type (Source_Irep)
                  else
                     Target_Itype);
               pragma Assert (Kind (Target_Itype) = Kind (Source_Itype));
               pragma Assert (Print_Msg ("Assignment_Op RHS Itype:"));
               pragma Assert (Print_Irep_Func (Target_Itype));
               pragma Assert (Print_Msg ("Assignment_Op LHS Itype:"));
               pragma Assert (Print_Irep_Func (Source_Itype));

               --  The source and target arrays may have equivalent types but
               --  may have different Ireps for each type.
               Source_Array : constant Irep :=
                 (if Source_Itype /= Target_Itype then
                     Make_Op_Typecast
                    (Op0             => Source_Irep,
                     Source_Location => Source_Location,
                     I_Type          => Target_Itype,
                     Range_Check     => False)
                  else
                     Source_Irep);

               Assignment : constant Irep :=
                 Make_Code_Assign
                   (Rhs             => Source_Array,
                    Lhs             => Target_Array,
                    Source_Location => Source_Location,
                    I_Type          => Target_Itype,
                    Range_Check     => False);
            begin
               Put_Line ("Static_Assignment");
               Append_Op (Block, Assignment);
            end;
         else
            --  Components have to be copied one at a time
            Put_Line ("From assinment op");
            declare
               Constrained_Source_Bounds :
               constant Static_And_Dynamic_Bounds :=
                 (if Source_Bounds.Is_Unconstrained then
                     Dest_Bounds
                  else
                     Source_Bounds);
            begin
               Check_Equal_Array_Lengths (Block, Source_Bounds, Dest_Bounds);
               Put_Line ("Array_Assignment_Op Copy array");
               Copy_Array
                 (Block         => Block,
                  Source_Type   => Source_Type,
                  Dest_Bounds   => Dest_Bounds,
                  Source_Bounds => Constrained_Source_Bounds,
                  Dest_Irep     => Target_Array,
                  Source_Irep   => Do_Expression (Source_Expr));
               Put_Line ("Array_Copied");
            end;
         end if;
      else
         Report_Unhandled_Node_Empty
           (N        => Dest_Node,
            Fun_Name => "Array_Assignment_Op",
            Message  => "Assignment to an unconstrained array object is " &
              "Unsupported");
      end if;
   end Array_Assignment_Op;

   procedure Array_Object_And_Friends (Array_Name : String;
                                       Array_Type : Entity_Id;
                                       Source_Loc : Irep;
                                       Block      : Irep)
   is
      pragma Assert (Print_Msg ("Array_Object_And_Friends"));
      Id            : constant Symbol_Id := Intern (Array_Name);
      pragma Assert (Print_Node (Array_Type));
      pragma Assert (Print_Msg ("Array_Object_And_Friends - Array_Type con: "
                       & Boolean'Image (Is_Constrained (Array_Type))));
      Bounds        : constant Static_And_Dynamic_Bounds :=
        Multi_Dimension_Flat_Bounds (Array_Type);
      pragma Assert (Print_Msg ("Bounds - Is_Unconstrained: " &
                       Boolean'Image (Bounds.Is_Unconstrained)));
      pragma Assert (Print_Irep_Func (Bounds.High_Dynamic));
      Needs_Size_Var : constant Boolean :=
        not Bounds.Has_Static_Bounds and then Is_Itype (Array_Type);

      pragma Assert (Print_Msg ("Array_Object_And_Friends"));
      pragma Assert (Print_Node (Array_Type));
      pragma Assert (Print_Msg ("Is_Itype " &
                       Boolean'Image (Is_Itype (Array_Type))));

      Array_Type_Pre  : constant Irep := Do_Type_Reference (Array_Type);
      Comp_Irep       : constant Irep := Get_Subtype (Array_Type_Pre);
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
         --  intialised in the goto code when the array subtype was declared.
         --  In either case the Irep array type from the Do_Type_Reference
         --  can be used.
            Array_Type_Pre
         else
         --  A new variable has to be declared to represent the size of
         --  the goto array object.
            Make_Array_Type
           (I_Subtype => Comp_Irep,
            Size      => Array_Size_Var));
      pragma Assert (Print_Irep_Func (Array_Type_Irep));
      pragma Assert (Print_Irep_Func (Get_Size (Array_Type_Irep)));
      pragma Assert (Print_Irep_Func (Get_Subtype (Array_Type_Irep)));

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
      if not Global_Symbol_Table.Contains (Id) then
         --  If a size variable is needed to define the size of the
         --  goto array object, declare it before the array.
         if Needs_Size_Var then
            declare
               Size_Decl : constant Irep := Make_Code_Decl
                 (Symbol          => Array_Size_Var,
                  Source_Location => Source_Loc,
                  I_Type          => Index_T,
                  Range_Check     => False);
               Size_Assg : constant Irep := Make_Code_Assign
                 (Rhs             =>
                    Make_Op_Add
                      (Rhs             => Index_T_One,
                       Lhs             => Bounds.High_Dynamic,
                       Source_Location => Source_Loc,
                       Overflow_Check  => False,
                       I_Type          => Index_T,
                       Range_Check     => False),
                  Lhs             => Array_Size_Var,
                  Source_Location => Source_Loc,
                  I_Type          => Index_T,
                  Range_Check     => False);
            begin
               Append_Op (Block, Size_Decl);
               Append_Op (Block, Size_Assg);
            end;
         end if;

         Append_Op (Block, Decl);
         New_Object_Symbol_Entry
           (Object_Name       => Id,
            Object_Type       => Array_Type_Irep,
            Object_Init_Value => Ireps.Empty,
            A_Symbol_Table    => Global_Symbol_Table);

         --  The model size of the object hast to be recorded.
         if ASVAT.Size_Model.Has_Static_Size (Array_Type) then
            ASVAT.Size_Model.Set_Static_Size
              (E          => Array_Type,
               Model_Size =>
                 ASVAT.Size_Model.Static_Size (Array_Type));
         else
            ASVAT.Size_Model.Set_Computed_Size
              (E         => Array_Type,
               Size_Expr =>
                 ASVAT.Size_Model.Computed_Size (Array_Type));
         end if;
         --  The first and last variables for each dimension have to
         --  added to the symbol table and initialised.
         Put_Line ("Declaring array friends for " & Array_Name);
         Print_Node_Briefly (Array_Type);
         Put_Line ("Is_Constrained: " &
                     Boolean'Image (Is_Constrained (Array_Type)));
         Put_Line ("Is_Constrained Etype: " &
                     Boolean'Image
                     (Is_Constrained (Etype (Array_Type))));

         Declare_Array_Friends
           (Array_Name => Array_Name,
            Array_Type => Array_Type,
            Block      => Block);
      end if;
   end Array_Object_And_Friends;

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

      Array_Bounds : Static_And_Dynamic_Bounds :=
        (if Is_Constrained (Target_Type) then
              Multi_Dimension_Flat_Bounds (Dec_Node)
         else
            Unconstrained_Bounds);

      Comp_Type        : constant Entity_Id :=
        Component_Type (Target_Type);

      Comp_Irep_Pre  : constant Irep :=
        Do_Type_Reference (Comp_Type);
      Comp_Irep      : constant Irep :=
        (if Kind (Follow_Symbol_Type
         (Comp_Irep_Pre, Global_Symbol_Table))
         = I_C_Enum_Type
         then
            Make_Unsignedbv_Type
           (ASVAT.Size_Model.Static_Size (Comp_Type))
         else
            Comp_Irep_Pre);

      The_Array    : Irep;
   begin
      Put_Line ("Array obj dec");
      if not Array_Bounds.Is_Unconstrained then
         Put_Line ("Array obj dec: Is_Constrained " &
                     Boolean'Image (Is_Constrained (Target_Type)));
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
                  Array_Length
               else
                  Make_Symbol_Expr
                 (Source_Location => Source_Loc,
                  I_Type          => Make_Unsignedbv_Type (64),
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
               Put_Line ("Declaration appended to the block");
               Print_Irep (Block);
               --  and assign the array length expression.
               Append_Op (Block,
                          Make_Code_Assign
                            (Rhs             =>
                               Make_Op_Typecast
                                 (Op0             => Array_Length,
                                  Source_Location => Source_Loc,
                                  I_Type          =>
                                    Make_Unsignedbv_Type (64),
                                  Range_Check     => False),
                             Lhs             => Arr_Len_Irep,
                             Source_Location => Source_Loc,
                             I_Type          => Make_Unsignedbv_Type (64),
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
         --  The array length, i.e. its goto I_Array_Type,
         --  for an unconstrained array object has to be determined from its
         --  initialization, which must be present.
         Make_Constrained_Array_From_Initialization
           (Block        => Block,
            Target_Type  => Target_Type,
            Array_Name   => Array_Name,
            Init_Expr    => Init_Expr,
            The_Array    => The_Array,
            Array_Bounds => Array_Bounds);

         --  Set the model size for the array object.
         ASVAT.Size_Model.Set_Computed_Size
           (E         => Target_Def,
            Size_Expr => Get_Size (Get_Type (The_Array)));

      end if;

      --  The array object should now be in the symbol table.
      pragma Assert (Global_Symbol_Table.Contains (Array_Id));

      --  Now do its initialization, if any.
      if Present (Init_Expr) then
         Put_Line ("From Do_Array_Object_Dec");
         Array_Assignment_Op
           (Source_Expr  => Init_Expr,
            Dest_Node    => Target_Def,
            Dest_Bounds  => Array_Bounds,
            Target_Array => The_Array,
            Block        => Block);
      end if;

      Put_Line ("End Do_Array_Object_Declaration");

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

   procedure Declare_Array_Friends (Array_Name : String;
                                    Array_Type : Entity_Id;
                                    Block      : Irep)
   is
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
   end Declare_Array_Friends;

   ----------------------------------------
   -- Declare_First_And_Last_From_Bounds --
   ----------------------------------------

   procedure Declare_First_Last_From_Bounds (Prefix     : String;
                                             Dimension  : String;
                                             Index_Type : Node_Id;
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

      Type_Irep : constant Irep :=
        Do_Type_Reference (Index_Type);

      First_Sym : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Type_Irep,
           Range_Check     => False,
           Identifier      => First_Name);
      Last_Sym : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Type_Irep,
           Range_Check     => False,
           Identifier      => Last_Name);

      Dec_First : constant Irep :=
        Make_Code_Decl
          (Symbol          => First_Sym,
           Source_Location => Source_Loc,
           I_Type          => Type_Irep,
           Range_Check     => False);

      Dec_Last : constant Irep :=
        Make_Code_Decl
          (Symbol          => Last_Sym,
           Source_Location => Source_Loc,
           I_Type          => Type_Irep,
           Range_Check     => False);

      First_Val : constant Irep :=
        (if Type_Irep = Index_T then
            Bounds.Low
         else
            Make_Op_Typecast
           (Op0             => Bounds.Low,
            Source_Location => Source_Loc,
            I_Type          => Type_Irep));

      Last_Val : constant Irep :=
        (if Type_Irep = Index_T then
            Bounds.High
         else
            Make_Op_Typecast
           (Op0             => Bounds.High,
            Source_Location => Source_Loc,
            I_Type          => Type_Irep));

      Assign_First : constant Irep :=
        Make_Code_Assign
          (Rhs             => First_Val,
           Lhs             => First_Sym,
           Source_Location => Source_Loc,
           I_Type          => Type_Irep,
           Range_Check     => False);

      Assign_Last : constant Irep :=
        Make_Code_Assign
          (Rhs             => Last_Val,
           Lhs             => Last_Sym,
           Source_Location => Source_Loc,
           I_Type          => Type_Irep,
           Range_Check     => False);
   begin
      --  Add the first and last variables to the symbol table.
      New_Object_Symbol_Entry
        (Object_Name       => First_Name_Id,
         Object_Type       => Type_Irep,
         Object_Init_Value => Bounds.Low,
         A_Symbol_Table    => Global_Symbol_Table);
      New_Object_Symbol_Entry
        (Object_Name       => Last_Name_Id,
         Object_Type       => Type_Irep,
         Object_Init_Value => Bounds.High,
         A_Symbol_Table    => Global_Symbol_Table);

      --  Declare and assign values in goto code.
      Append_Op (Block, Dec_First);
      Append_Op (Block, Dec_Last);
      Append_Op (Block, Assign_First);
      Append_Op (Block, Assign_Last);
   end Declare_First_Last_From_Bounds;

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

      Bounds : constant Dimension_Bounds := Get_Bounds (Index);
   begin
      Declare_First_Last_From_Bounds
        (Prefix     => Prefix,
         Dimension  => Number_Str,
         Index_Type => Index_Type,
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
      Component_Pre     : constant Irep :=
        Do_Type_Reference (Component_Type (Aggregate_Subtype));
      Component_Irep    : constant Irep :=
        (if Kind (Follow_Symbol_Type (Component_Pre,
         Global_Symbol_Table)) = I_C_Enum_Type
         then
            Make_Unsignedbv_Type
           (ASVAT.Size_Model.Static_Size (Component_Type (Aggregate_Subtype)))
         else
            Component_Pre);
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
      Put_Line ("Do_Aggregate_Array_Literal");
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
         declare
            Bounds : constant Dimension_Bounds :=
              Get_Dimension_Bounds (N, 1, Aggregate_Bounds (N));
         begin
            if Positional_Assoc then
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

--     function Do_Aggregate_Literal_Array (N : Node_Id) return Irep is
--        Result_Type : constant Irep := Do_Type_Reference (Etype (N));
--
--        function Build_Array_Lit_Func_Body (N : Node_Id) return Irep
--          with Pre => Ekind (Etype (N)) in E_Array_Type | E_Array_Subtype,
--          Post => Kind (Build_Array_Lit_Func_Body'Result) = I_Code_Block;
--
--        function Build_Array_Lit_Func (N : Node_Id) return Symbol
--          with Pre => Ekind (Etype (N)) in E_Array_Type | E_Array_Subtype,
--          Post => not (Build_Array_Lit_Func'Result.Value = Ireps.Empty);
--
--        function Make_No_Args_Func_Call_Expr (Fun_Symbol : Irep;
--                                              Return_Type : Irep;
--                                              Source_Loc : Irep)
--                                              return Irep
--          with Pre => (Kind (Fun_Symbol) = I_Symbol_Expr
--                       and then Kind (Return_Type) in Class_Type),
--          Post => Kind (Make_No_Args_Func_Call_Expr'Result) =
--          I_Side_Effect_Expr_Function_Call;
--
--        -------------------------------
--        -- Build_Array_Lit_Func_Body --
--        -------------------------------
--
--        --  build the following function:
--        --  struct array_struct {int first1; int last1; array_type* data; }
--        --  array_lit() {
--        --    array_type temp_literal[high_bound - low_bound + 1];
--        --    temp_literal = { literal_1, .. literal_n };
--     --    struct arrays_struct { int first1; int last1; array_type *data; }
--        --      temp_array;
--        --    temp_array.first1 = low_bound;
--        --    temp_array.last1 = high_bound;
--      --    temp_array.data = (array_type *)malloc((high_bound-low_bound+1)*
--        --                                           sizeof(array_type));
--        --    temp_lhs = memcpy(temp_array.data,
--        --                      &temp_literal,
--      --                      (high_bound-low_bound+1)*sizeof(array_type)));
--        --    return temp_array;
--        --  }
--        function Build_Array_Lit_Func_Body (N : Node_Id) return Irep is
--
--           Pos_Iter : Node_Id := First (Expressions (N));
--           Source_Loc : constant Irep := Get_Source_Location (N);
--           Bounds : constant Node_Id := Aggregate_Bounds (N);
--           Low_Expr : constant Irep :=
--             Typecast_If_Necessary (Do_Expression (Low_Bound (Bounds)),
--                                    CProver_Size_T, Global_Symbol_Table);
--           High_Expr : constant Irep :=
--             Typecast_If_Necessary (Do_Expression (High_Bound (Bounds)),
--                                    CProver_Size_T, Global_Symbol_Table);
--           Len_Expr : constant Irep :=
--             Build_Array_Size (First      => Low_Expr,
--                               Last       => High_Expr);
--       Element_Type_Ent : constant Entity_Id := Get_Array_Component_Type (N);
--           Element_Type_Pre : constant Irep :=
--             Do_Type_Reference (Element_Type_Ent);
--
--           Element_Type : constant Irep :=
--             (if Kind (Follow_Symbol_Type (Element_Type_Pre,
--              Global_Symbol_Table)) = I_C_Enum_Type
--              then
--                 Make_Unsignedbv_Type
--                (ASVAT.Size_Model.Static_Size (Element_Type_Ent))
--              else
--                 Element_Type_Pre);
--           Element_Size : constant Uint :=
--             (if Kind (Element_Type) in Class_Bitvector_Type
--              then
--                 UI_From_Int (Int (Get_Width (Element_Type)))
--              else
--                 Esize (Element_Type_Ent));
--           Literal_Temp : constant Irep :=
--             Fresh_Var_Symbol_Expr (Make_Pointer_Type (Element_Type),
--                                    "array_literal");
--           Array_Temp : constant Irep :=
--             Fresh_Var_Symbol_Expr (Result_Type, "temp_array");
--           Lhs_Temp : constant Irep :=
--             Fresh_Var_Symbol_Expr (Make_Pointer_Type (Element_Type),
--                                    "temp_lhs");
--           Result_Block : constant Irep :=
--             Make_Code_Block (Source_Loc, CProver_Nil_T);
--           Pos_Number : Natural := 0;
--
--           --  NB: Component number seem to be ignored by CBMC
--           --  We represent arrays as a structure of 3 members:
--           --  0: first index
--           --  1: last index
--           --  2: data pointer
--           Data_Mem_Expr : constant Irep := Get_Data_Member (Array_Temp,
--                                                        Global_Symbol_Table);
--           Array_Temp_Struct : constant Irep :=
--             Make_Struct_Expr (Source_Location => Source_Loc,
--                               I_Type          => Result_Type);
--           Raw_Malloc_Call : constant Irep :=
--             Make_Malloc_Function_Call_Expr (Num_Elem          => Len_Expr,
--                                         Element_Type_Size => Element_Size,
--                                          Source_Loc        => Source_Loc);
--           Malloc_Call_Expr : constant Irep :=
--             Typecast_If_Necessary (Raw_Malloc_Call,
--                                    Make_Pointer_Type (Element_Type),
--                                    Global_Symbol_Table);
--           Literal_Address : constant Irep :=
--             Typecast_If_Necessary (Literal_Temp,
--                                    Make_Pointer_Type (Element_Type),
--                                    Global_Symbol_Table);
--           Memcpy_Call_Expr : constant Irep :=
--         Make_Memcpy_Function_Call_Expr (Destination       => Data_Mem_Expr,
--                                       Source            => Literal_Address,
--                                           Num_Elem          => Len_Expr,
--                                           Element_Type_Size => Element_Size,
--                                          Source_Loc        => Source_Loc);
--
--           PElement_Type : constant Irep := Make_Pointer_Type (Element_Type);
--
--           procedure Initialize_Array;
--           procedure Initialize_Array is
--              Raw_Malloc_Call : constant Irep :=
--             Make_Malloc_Function_Call_Expr (Num_Elem          => Len_Expr,
--                                                Element_Type_Size =>
--                                                  Element_Size,
--                                           Source_Loc        => Source_Loc);
--              Malloc_Call_Expr : constant Irep :=
--                Typecast_If_Necessary (Raw_Malloc_Call,
--                                       Make_Pointer_Type (Element_Type),
--                                       Global_Symbol_Table);
--              Others_Expression : Irep;
--
--              Loop_Iter_Var : constant Irep :=
--                Fresh_Var_Symbol_Expr (CProver_Size_T, "i");
--              Loop_Cond : constant Irep :=
--                Make_Op_Gt (Rhs             => Loop_Iter_Var,
--                            Lhs             => Len_Expr,
--                            Source_Location => Source_Loc,
--                            Overflow_Check  => False,
--                            I_Type          => Make_Bool_Type);
--              Size_T_Zero : constant Irep :=
--                Build_Index_Constant (Value      => 0,
--                                      Source_Loc => Source_Loc);
--              Size_T_One : constant Irep :=
--                Build_Index_Constant (Value      => 1,
--                                      Source_Loc => Source_Loc);
--              Increment_I : constant Irep :=
--                Make_Op_Add (Rhs             => Size_T_One,
--                             Lhs             => Loop_Iter_Var,
--                             Source_Location => Source_Loc,
--                             Overflow_Check  => False,
--                             I_Type          => CProver_Size_T);
--              Loop_Iter : constant Irep :=
--                Make_Code_Assign (Rhs             => Increment_I,
--                                  Lhs             => Loop_Iter_Var,
--                                  Source_Location => Source_Loc,
--                                  I_Type          => Make_Nil_Type);
--              Loop_Body : constant Irep :=
--                Make_Code_Block (Source_Location => Source_Loc,
--                                 I_Type          => Make_Nil_Type);
--
--              Array_As_Pointer : constant Irep :=
--                Typecast_If_Necessary (Literal_Temp, PElement_Type,
--                                       Global_Symbol_Table);
--              Lhs_Ptr : constant Irep :=
--                Make_Op_Add (Rhs             => Loop_Iter_Var,
--                             Lhs             => Array_As_Pointer,
--                             Source_Location => Source_Loc,
--                             Overflow_Check  => False,
--                             I_Type          => PElement_Type);
--              Lhs_Irep : constant Irep :=
--                Make_Dereference_Expr (Object          => Lhs_Ptr,
--                                       Source_Location => Source_Loc,
--                                       I_Type          => Element_Type);
--           begin
--              Append_Declare_And_Init (Symbol     => Literal_Temp,
--                                       Value      => Malloc_Call_Expr,
--                                       Block      => Result_Block,
--                                       Source_Loc => Source_Loc);
--
--              --  Handle an "others" splat expression if present:
--              if Present (Component_Associations (N)) then
--                 declare
--                    Maybe_Others_Node : constant Node_Id :=
--                      Last (Component_Associations (N));
--                    Maybe_Others_Choices : constant List_Id :=
--                      Choices (Maybe_Others_Node);
--                 begin
--                    pragma Assert (List_Length (Maybe_Others_Choices) = 1);
--
--                    --  this association does not end with others -> bail
--                if Nkind (First (Maybe_Others_Choices)) /= N_Others_Choice
--                    then
--                       return;
--                    end if;
--
--                    Others_Expression :=
--                      Do_Expression (Expression (Maybe_Others_Node));
--                 end;
--              else
--                 return;
--              end if;
--
--              --  iterate over elements and assing others-value to them
--              Append_Op (Loop_Body,
--                    Make_Code_Assign (Rhs             => Others_Expression,
--                                           Lhs             => Lhs_Irep,
--                                           Source_Location => Source_Loc,
--                                        I_Type          => Make_Nil_Type));
--              Append_Op (Loop_Body, Loop_Iter);
--
--              Append_Op (Result_Block,
--                         Make_Code_Assign (Rhs             => Size_T_Zero,
--                                           Lhs             => Loop_Iter_Var,
--                                           Source_Location => Source_Loc,
--                                        I_Type          => Make_Nil_Type));
--              Append_Op (Result_Block,
--                         Make_Code_While (Loop_Body       => Loop_Body,
--                                          Cond            => Loop_Cond,
--                                          Source_Location => Source_Loc,
--                                          I_Type          => Make_Nil_Type));
--           end Initialize_Array;
--
--        begin
--           Initialize_Array;
--
--           while Present (Pos_Iter) loop
--              declare
--                 Expr : constant Irep := Do_Expression (Pos_Iter);
--                 Pos_Constant : constant Irep :=
--                   Build_Index_Constant (Value      => Int (Pos_Number),
--                                         Source_Loc => Source_Loc);
--                 Array_As_Pointer : constant Irep :=
--                   Typecast_If_Necessary (Literal_Temp, PElement_Type,
--                                          Global_Symbol_Table);
--                 Lhs_Ptr : constant Irep :=
--                   Make_Op_Add (Rhs             => Pos_Constant,
--                                Lhs             => Array_As_Pointer,
--                                Source_Location => Source_Loc,
--                                Overflow_Check  => False,
--                                I_Type          => PElement_Type);
--                 Lhs_Irep : constant Irep :=
--                   Make_Dereference_Expr (Object          => Lhs_Ptr,
--                                          Source_Location => Source_Loc,
--                                          I_Type          => Element_Type);
--              begin
--                 Append_Op (Result_Block,
--                            Make_Code_Assign (Rhs             =>
--           Typecast_If_Necessary (Expr, Element_Type, Global_Symbol_Table),
--                                              Lhs             => Lhs_Irep,
--                                              Source_Location => Source_Loc,
--                                        I_Type          => Element_Type));
--              end;
--              Next (Pos_Iter);
--              Pos_Number := Pos_Number + 1;
--           end loop;
--
--           Append_Struct_Member (Array_Temp_Struct, Low_Expr);
--           Append_Struct_Member (Array_Temp_Struct, High_Expr);
--           Append_Struct_Member (Array_Temp_Struct, Malloc_Call_Expr);
--
--           if Present (Component_Associations (N)) and then
--             List_Length (Component_Associations (N)) /= 1
--           then
--              declare
--                 Components : constant List_Id := Component_Associations (N);
--                 Component_Node : Node_Id := First (Components);
--              begin
--                 if List_Length (Choices (Component_Node)) /= 1 then
--                    return Report_Unhandled_Node_Irep (N,
--                                       "Do_Aggregate_Literal_Array",
--                                   "More than one choice in component node");
--                 end if;
--                 while Present (Component_Node) loop
--                    declare
--                       Expr : constant Irep :=
--                         Do_Expression (Expression (Component_Node));
--                       Choice_Id : constant Irep :=
--                         Do_Expression (First (Choices (Component_Node)));
--                       Component_Index : constant Irep :=
--                         Typecast_If_Necessary (Choice_Id, CProver_Size_T,
--                                                Global_Symbol_Table);
--                       Zero_Based_Index : constant Irep :=
--                         Make_Op_Sub (Rhs             => Low_Expr,
--                                      Lhs             => Component_Index,
--                                      Source_Location => Source_Loc,
--                                      Overflow_Check  => False,
--                                      I_Type          => CProver_Size_T);
--                       Array_As_Pointer : constant Irep :=
--                         Typecast_If_Necessary (Literal_Temp, PElement_Type,
--                                                Global_Symbol_Table);
--                       Lhs_Ptr : constant Irep :=
--                         Make_Op_Add (Rhs             => Zero_Based_Index,
--                                      Lhs             => Array_As_Pointer,
--                                      Source_Location => Source_Loc,
--                                      Overflow_Check  => False,
--                                      I_Type          => PElement_Type);
--                       Lhs_Irep : constant Irep :=
--                         Make_Dereference_Expr (Object          => Lhs_Ptr,
--                                            Source_Location => Source_Loc,
--                                           I_Type          => Element_Type);
--                    begin
--                       Append_Op (Result_Block,
--                                  Make_Code_Assign (Rhs             =>
--            Typecast_If_Necessary (Expr, Element_Type, Global_Symbol_Table),
--                                              Lhs             => Lhs_Irep,
--                                              Source_Location => Source_Loc,
--                                           I_Type          => Element_Type));
--                    end;
--                    Component_Node := Next (Component_Node);
--                 end loop;
--              end;
--           end if;
--
--         --  As long as symex is field-insensitive we need to initialise the
--         --  array structure with the information about allocated size.
--         --  I.e. Create a temporary struct and assign it in one swoop to
--      --  Array_Temp - so that Symex does not see the struct as having been
--       --  changed after its creation and can therefore see it as constant -
--      --  which means that the struct member that refers to "allocated size"
--         --  remains visible/accessible.
--           Append_Declare_And_Init (Symbol     => Array_Temp,
--                                    Value      => Array_Temp_Struct,
--                                    Block      => Result_Block,
--                                    Source_Loc => Source_Loc);
--           Append_Op (Result_Block,
--                      Make_Code_Assign (Rhs             => Memcpy_Call_Expr,
--                                        Lhs             => Lhs_Temp,
--                                        Source_Location => Source_Loc));
--           Append_Op (Result_Block,
--                      Make_Code_Return (Return_Value    => Array_Temp,
--                                        Source_Location => Source_Loc));
--
--           return Result_Block;
--        end Build_Array_Lit_Func_Body;
--
--        --------------------------
--        -- Build_Array_Lit_Func --
--        --------------------------
--
--        function Build_Array_Lit_Func (N : Node_Id) return Symbol is
--           Func_Name : constant String := Fresh_Var_Name ("array_lit");
--           Func_Params : constant Irep := Make_Parameter_List;
--           Func_Type : constant Irep :=
--             Make_Code_Type (Parameters  => Func_Params,
--                             Ellipsis    => False,
--                             Return_Type => Do_Type_Reference (Etype (N)),
--                             Inlined     => False,
--                             Knr         => False);
--        begin
--           return New_Function_Symbol_Entry (Name        => Func_Name,
--                                             Symbol_Type => Func_Type,
--                                             Value       =>
--                                               Build_Array_Lit_Func_Body (N),
--                                             A_Symbol_Table =>
--                                               Global_Symbol_Table);
--        end Build_Array_Lit_Func;
--
--        -----------------------------------
--        -- Make_Array_Lit_Func_Call_Expr --
--        -----------------------------------
--
--        function Make_No_Args_Func_Call_Expr (Fun_Symbol : Irep;
--                                              Return_Type : Irep;
--                                              Source_Loc : Irep)
--                                              return Irep is
--           Call_Args  : constant Irep := Make_Argument_List;
--           Fun_Call : constant Irep :=
--             Make_Side_Effect_Expr_Function_Call (
--                                                Arguments       => Call_Args,
--                                              I_Function      => Fun_Symbol,
--                                              Source_Location => Source_Loc,
--                                             I_Type          => Return_Type);
--        begin
--           return Fun_Call;
--        end Make_No_Args_Func_Call_Expr;
--
--        Func_Symbol : constant Symbol := Build_Array_Lit_Func (N);
--     begin
--        return Make_No_Args_Func_Call_Expr
--          (Fun_Symbol  =>
--             Symbol_Expr (Func_Symbol),
--           Return_Type => Result_Type,
--           Source_Loc  => Get_Source_Location (N));
--     end Do_Aggregate_Literal_Array;

   ------------------------------------
   -- Make_Array_Default_Initialiser --
   ------------------------------------

   --  temp_comment: this was a nested function of 'do_object_declaration) but
   --  is pure

   function Make_Array_Default_Initialiser (E : Entity_Id) return Irep is
      --  Note this function only works for one dimensional arrays at present.
      Idx : constant Node_Id := First_Index (E);
      --  The Entity is an array object
      --  The first index is a discrete_subtype_definition which
      --  may be a subtype_indication or a range.
      --  For determining the upper bounds and lower bounds a range is required
      --  and if the first index is a subtype_indication, the constraints
      --  of the subtype have to be obtained - which should be a range.
      Bound_Range : constant Node_Id :=
        (if Nkind (Idx) = N_Range
         then
            --  It is a range
            Idx
         elsif Nkind (Idx) = N_Subtype_Indication then
            --  It is an anonymous subtype
            Scalar_Range (Etype (Idx))
         else
            --  It is an explicitly declared subtype
            Scalar_Range (Entity (Idx)));

      Lbound : constant Irep :=
        Typecast_If_Necessary (Do_Expression (Low_Bound (Bound_Range)),
                               CProver_Size_T, Global_Symbol_Table);
      Hbound : constant Irep :=
        Typecast_If_Necessary (Do_Expression (High_Bound (Bound_Range)),
                               CProver_Size_T, Global_Symbol_Table);
      Source_Loc : constant Irep := Get_Source_Location (E);
      Len : constant Irep :=
        Build_Array_Size (First      => Lbound,
                          Last       => Hbound);
      Component_Type : constant Irep :=
        Do_Type_Reference (Get_Array_Component_Type (E));
      Alloc : constant Irep :=
        Make_Malloc_Function_Call_Expr (Num_Elem          => Len,
                                        Element_Type_Size =>
                                          Esize (Get_Array_Component_Type (E)),
                                        Source_Loc        => Source_Loc);
      Ret : constant Irep :=
        Make_Struct_Expr (Source_Location => Source_Loc,
                          I_Type          => Do_Type_Reference (E));
      Comp_P_Type : constant Irep :=
        Make_Pointer_Type (I_Subtype => Component_Type,
                           Width     => Pointer_Type_Width);
   begin
      Append_Struct_Member (Ret, Lbound);
      Append_Struct_Member (Ret, Hbound);
      Append_Struct_Member (Ret,
                            Typecast_If_Necessary (Alloc, Comp_P_Type,
                              Global_Symbol_Table));
      return Ret;
   end Make_Array_Default_Initialiser;

--     ----------------------
--     -- Do_Array_Object --
--     ----------------------
--
--     procedure Do_Array_Object (Object_Node     : Node_Id;
--                                Object_Ada_Type : Entity_Id;
--                                Subtype_Irep    : out Irep)
--     is
--     begin
--        Subtype_Irep :=
--          Make_Array_Subtype
--            (Declaration    => Object_Node,
--             Is_Constrained => True,  -- Object declarations are constrained.
--             First_Index    => First_Index (Object_Ada_Type),
--           Component_Type => Get_Non_Array_Component_Type (Object_Ada_Type));
--     end Do_Array_Object;

   ----------------------
   -- Do_Array_Subtype --
   ----------------------

   function Do_Array_Subtype (Subtype_Node : Node_Id;
                              The_Entity   : Entity_Id) return Irep
   is
   begin
      Put_Line ("The entity is constrained " &
                  Boolean'Image (Is_Constrained (The_Entity)));
      Print_Node_Briefly (The_Entity);
      Print_Node_Briefly (Subtype_Node);
      return
      (if Is_Constrained (The_Entity) then
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
         (Make_Constrained_Array_Subtype
        (Declaration    => Parent (N)));

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

   -------------------------
   -- Do_Array_Assignment --
   -------------------------

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
   function Do_Array_Assignment (N : Node_Id) return Irep
   is
      --  We assume the lhs is allocated
      LHS_Node : constant Node_Id := Name (N);
      RHS_Node : constant Node_Id := Expression (N);

      Source_Loc : constant Irep := Get_Source_Location (N);
      Ret_Type : constant Irep := Make_Void_Type;
      RHS_Arrays : constant Irep_Array := Do_RHS_Array_Assign (RHS_Node);
      Result_Type : constant Irep := Do_Type_Reference (Etype (LHS_Node));
      Concat_Params : constant Irep := Make_Parameter_List;
      Concat_Arguments : constant Irep := Make_Argument_List;
      Elem_Type_Ent : constant Entity_Id :=
        Get_Array_Component_Type (LHS_Node);
      Element_Type : constant Irep := Do_Type_Reference (Elem_Type_Ent);
      --  Unique name given by Build_Function.
      Function_Name : constant String := "concat_assign";

      Destination : constant Irep :=
        Create_Fun_Parameter (Fun_Name        => Function_Name,
                              Param_Name      => "dest_array",
                              Param_Type      => Result_Type,
                              Param_List      => Concat_Params,
                              A_Symbol_Table  => Global_Symbol_Table,
                              Source_Location => Source_Loc);

      function Build_Array_Params return Irep_Array;
      function Build_Concat_Assign_Body return Irep;

      function Build_Array_Params return Irep_Array
      is
         Result_Array : Irep_Array (RHS_Arrays'Range);
      begin
         for I in RHS_Arrays'Range loop
            Result_Array (I) :=
              Create_Fun_Parameter (Fun_Name        => Function_Name,
                                    Param_Name      => "array_rhs",
                                    Param_Type      => Result_Type,
                                    Param_List      => Concat_Params,
                                    A_Symbol_Table  => Global_Symbol_Table,
                                    Source_Location => Source_Loc);
         end loop;
         return Result_Array;
      end Build_Array_Params;

      function Build_Concat_Assign_Body return Irep
      is
         Slices : constant Irep_Array := Build_Array_Params;
         Result_Block : constant Irep :=
           Make_Code_Block (Source_Loc, CProver_Nil_T);
         Dest_Symbol : constant Irep := Param_Symbol (Destination);
         PElement_Type : constant Irep :=
           Make_Pointer_Type (Element_Type, Pointer_Type_Width);

         Dest_Data : constant Irep := Get_Data_Member (Dest_Symbol,
                                                       Global_Symbol_Table);
         Current_Offset : constant Irep :=
           Fresh_Var_Symbol_Expr (CProver_Size_T, "offset_step");

         Void_Ptr_Type : constant Irep :=
           Make_Pointer_Type (I_Subtype => Make_Void_Type,
                              Width     => Pointer_Type_Width);
         Memcpy_Lhs : constant Irep :=
           Fresh_Var_Symbol_Expr (Void_Ptr_Type, "memcpy_lhs");
         Zero : constant Irep :=
           Build_Index_Constant (Value      => 0,
                                 Source_Loc => Source_Loc);
         EType_Size : constant Uint := Esize (Elem_Type_Ent);

         Sum_Size_Var : constant Irep :=
           Fresh_Var_Symbol_Expr (CProver_Size_T, "sum_size");
         Dest_Temp_Pre_Alloc : constant Irep :=
           Make_Malloc_Function_Call_Expr (
                                           Num_Elem          => Sum_Size_Var,
                                           Element_Type_Size => EType_Size,
                                           Source_Loc        => Source_Loc);
         Dest_Temp_Alloc : constant Irep :=
           Typecast_If_Necessary (Dest_Temp_Pre_Alloc, PElement_Type,
                                  Global_Symbol_Table);
         Dest_Temp : constant Irep :=
           Fresh_Var_Symbol_Expr (PElement_Type, "dest_temp");

         procedure Build_Sum_Size (Ith_Slice : Irep);

         procedure Build_Sum_Size (Ith_Slice : Irep) is
            Source_I_Symbol : constant Irep := Param_Symbol (Ith_Slice);
            Slice_Size : constant Irep :=
              Build_Array_Size (Source_I_Symbol);
            Size_Increment : constant Irep :=
              Make_Op_Add (Rhs             =>
                             Typecast_If_Necessary (Slice_Size, CProver_Size_T,
                               Global_Symbol_Table),
                           Lhs             => Sum_Size_Var,
                           Source_Location => Source_Loc,
                           Overflow_Check  => False,
                           I_Type          => CProver_Size_T);
         begin
            Append_Op (Result_Block,
                       Make_Code_Assign (Rhs             => Size_Increment,
                                         Lhs             => Sum_Size_Var,
                                         Source_Location => Source_Loc));
         end Build_Sum_Size;

         procedure Process_Slice (Ith_Slice : Irep);

         --  Allocate a temporary, memcpy into the temporary, compute offset
         --  for destination, memcpy into the destination
         procedure Process_Slice (Ith_Slice : Irep)
         is
            Source_I_Symbol : constant Irep := Param_Symbol (Ith_Slice);
            Slice_Size : constant Irep :=
              Build_Array_Size (Source_I_Symbol);
            Slice_Size_Var : constant Irep :=
              Fresh_Var_Symbol_Expr (CProver_Size_T, "slice_size");
            Offset_Dest : constant Irep :=
              Make_Op_Add (Rhs             => Current_Offset,
                           Lhs             => Dest_Temp,
                           Source_Location => Source_Loc,
                           Overflow_Check  => False,
                           I_Type          => PElement_Type);
            Left_Data : constant Irep := Get_Data_Member (Source_I_Symbol,
                                                          Global_Symbol_Table);

            Memcpy_Fin : constant Irep :=
              Make_Memcpy_Function_Call_Expr (
                                          Destination       => Offset_Dest,
                                          Source            => Left_Data,
                                          Num_Elem          => Slice_Size_Var,
                                          Element_Type_Size => EType_Size,
                                          Source_Loc        => Source_Loc);
            Size_Increment : constant Irep :=
              Make_Op_Add (Rhs             => Slice_Size_Var,
                           Lhs             => Current_Offset,
                           Source_Location => Source_Loc,
                           I_Type          => CProver_Size_T);
         begin
            Append_Op (Result_Block,
                       Make_Code_Assign (Rhs             => Slice_Size,
                                         Lhs             => Slice_Size_Var,
                                         Source_Location => Source_Loc));
            Append_Op (Result_Block,
                       Make_Code_Assign (Rhs             => Memcpy_Fin,
                                         Lhs             => Memcpy_Lhs,
                                         Source_Location => Source_Loc));
            Append_Op (Result_Block,
                       Make_Code_Assign (Rhs             => Size_Increment,
                                         Lhs             => Current_Offset,
                                         Source_Location => Source_Loc));
         end Process_Slice;

         Memcpy_Dest : constant Irep :=
           Make_Memcpy_Function_Call_Expr (
                                           Destination       => Dest_Data,
                                           Source            => Dest_Temp,
                                           Num_Elem          => Sum_Size_Var,
                                           Element_Type_Size => EType_Size,
                                           Source_Loc        => Source_Loc);
      begin
         Append_Op (Result_Block,
                    Make_Code_Assign (Rhs             => Zero,
                                      Lhs             => Current_Offset,
                                      Source_Location => Source_Loc));
         Append_Op (Result_Block,
                    Make_Code_Assign (Rhs             =>
                                        Typecast_If_Necessary (Zero,
                                          CProver_Size_T, Global_Symbol_Table),
                                  Lhs             => Sum_Size_Var,
                                  Source_Location => Source_Loc));
         for I in Slices'Range loop
            Build_Sum_Size (Slices (I));
         end loop;
         Append_Op (Result_Block,
                    Make_Code_Assign (Rhs             => Dest_Temp_Alloc,
                                      Lhs             => Dest_Temp,
                                      Source_Location => Source_Loc));
         for I in Slices'Range loop
            Process_Slice (Slices (I));
         end loop;
         Append_Op (Result_Block,
                    Make_Code_Assign (Rhs             => Memcpy_Dest,
                                      Lhs             => Memcpy_Lhs,
                                      Source_Location => Source_Loc));
         return Result_Block;
      end Build_Concat_Assign_Body;

      Func_Symbol : constant Symbol :=
        Build_Function (Name           => Function_Name,
                        RType          => Ret_Type,
                        Func_Params    => Concat_Params,
                        FBody          => Build_Concat_Assign_Body,
                        A_Symbol_Table => Global_Symbol_Table);

      Func_Call : constant Irep :=
        Make_Side_Effect_Expr_Function_Call (
                                  Arguments       => Concat_Arguments,
                                  I_Function      => Symbol_Expr (Func_Symbol),
                                  Source_Location => Source_Loc,
                                  I_Type          => Ret_Type);
      Concat_Lhs : constant Irep :=
        Fresh_Var_Symbol_Expr (Ret_Type, "concat_Lhs");
   begin
      Put_Line ("Into do_array_assignment");
      Append_Argument (Concat_Arguments,
                       Do_Expression (LHS_Node));
      for I in RHS_Arrays'Range loop
         Append_Argument (Concat_Arguments,
                          RHS_Arrays (I));
      end loop;

      return Make_Code_Assign (Rhs             => Func_Call,
                               Lhs             => Concat_Lhs,
                               Source_Location => Source_Loc);
   end Do_Array_Assignment;

   function Do_RHS_Array_Assign (N : Node_Id) return Irep_Array
   is
   begin
      Put_Line ("Do_RHS_Array_Assign Start");
      if not (Nkind (N) = N_Op_Concat) then
         Put_Line ("Do_RHS_Array_Assign End");
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

   function Do_Array_First_Last_Length (N : Node_Id; Attr : Attribute_Id)
                                        return Irep
   is
      Source_Loc  : constant Irep := Get_Source_Location (N);
      The_Prefix  : constant Node_Id := Prefix (N);
      Attr_Expr   : constant Node_Id := First (Expressions (N));
      Dimension   : constant Integer :=
        (if Present (Attr_Expr) then
         --  Ada rules require the dimension expression to be static.
            Integer (UI_To_Int (Intval (Attr_Expr)))
         else
         --  No dimension expression defaults to dimension 1
            1);
   begin
      Put_Line ("**** Do_Array_First_Last_Length");
      Put_Line (Attribute_Id'Image (Attr));
      Print_Node_Briefly (N);
      Print_Node_Briefly (The_Prefix);
      Print_Node_Briefly (Attr_Expr);
      if Nkind (The_Prefix) in N_Has_Entity then
         declare
            The_Entity  : constant Entity_Id := Entity (The_Prefix);
            Arr_Subtype : constant Entity_Id := Etype (The_Entity);
            pragma Assert (Print_Node (N));
            pragma Assert (Print_Node (The_Prefix));
            pragma Assert (Print_Node (The_Entity));
            pragma Assert (Print_Node (Etype (N)));
            pragma Assert (Print_Node (Arr_Subtype));
            pragma Assert (Print_Msg ("Is an array (The_Entity) " &
                             Boolean'Image
                             (Is_Array_Type (Etype (The_Entity)))));
            pragma Assert (Print_Msg ("Is constrained (The_Entity) " &
                             Boolean'Image (Is_Constrained (The_Entity))));
            pragma Assert (Print_Msg ("Is constrained (Etype (The_Entity)) " &
                             Boolean'Image
                             (Is_Constrained (Etype (The_Entity)))));
            pragma Assert (Print_Msg ("Is a parameter (The_Entity) " &
                             Boolean'Image (Is_Formal (The_Entity))));
            Bounds      : constant Dimension_Bounds :=
              (if not Is_Constrained (Arr_Subtype) then
               --  It must be an unconstrained array.
               --  Use the extra variables or parameters associated
               --  with the array.
                  Do_Unconstrained_First_Last
                 (The_Entity, Dimension, Source_Loc)
               else
               --  Use the subtype definition which will be constrained.
                  Do_Constrained_First_Last (Arr_Subtype, Dimension));

            pragma Assert (Print_Irep_Func (Bounds.Low));
            pragma Assert (Print_Irep_Func (Bounds.High));
         begin
            --        Print_Node_Briefly (Etype (Prefix (N)));
            Print_Node_Briefly (Entity (The_Prefix));

            if Present (Attr_Expr) then
               Put_Line ("The dimension is " &
                           Int'Image (UI_To_Int (Intval (Attr_Expr))));
            else
               Put_Line ("No Dimension");
            end if;
            Print_Node_Briefly (The_Entity);
            Print_Node_Briefly (Etype (The_Prefix));
            Print_Node_Briefly (Etype (The_Entity));
            Put_Line ("The attribute is " &
                        Attribute_Id'Image (Attr));
            return
              (case Attr is
                  when Attribute_First => Bounds.Low,
                  when Attribute_Last => Bounds.High,
                  when others => Calculate_Dimension_Length (Bounds));

         end;
      else
         Put_Line ("The Prefix is not an array");
         Print_Node_Subtree (The_Prefix);
         if Nkind (The_Prefix) = N_Function_Call then
            declare
               Prefix_Etype : constant Entity_Id :=
                 Etype (The_Prefix);
            begin
               if Is_Array_Type (Prefix_Etype) then
                  if Is_Constrained (Prefix_Etype) then
                     declare
                        Bounds : constant Dimension_Bounds :=
                          Do_Constrained_First_Last (Prefix_Etype, Dimension);
                     begin
                        return
                          (case Attr is
                              when Attribute_First => Bounds.Low,
                              when Attribute_Last => Bounds.High,
                              when others =>
                                 Calculate_Dimension_Length (Bounds));
                     end;
                  else
                     declare
                        Res_Arr : constant Irep :=
                          Do_Expression (The_Prefix);
                     begin
                        Put_Line ("The return irep");
                        Print_Irep (Res_Arr);
                        Print_Irep (Get_Type (Res_Arr));
                     end;

                     return
                       Report_Unhandled_Node_Irep
                         (N        => The_Prefix,
                          Fun_Name => "Do_Array_First_Last_Length",
                          Message  => "Unconstrainned array");
                  end if;
               else
                  return
                    Report_Unhandled_Node_Irep
                      (N        => The_Prefix,
                       Fun_Name => "Do_Array_First_Last_Length",
                       Message  => "The function result is not an array");
               end if;
            end;
         else
            return
              Report_Unhandled_Node_Irep
                (N        => The_Prefix,
                 Fun_Name => "Do_Array_First_Last_Length",
                 Message  => "oops");
         end if;
      end if;
   end Do_Array_First_Last_Length;

   function Do_Constrained_First_Last (E : Entity_Id;
                                       Dimension : Positive)
                                       return Dimension_Bounds
   is
      Dim_Index : Node_Id := First_Index (E);
   begin
      Put_Line ("A constrained_Array");
      --  Get the right index for the dimension
      for I in 2 .. Dimension loop
         Dim_Index := Next_Index (Dim_Index);
      end loop;

      Put_Line ("The Index is");
      Print_Node_Briefly (Dim_Index);
      --  Now get the lower and upper bounds of the dimension
      return
        Get_Dimension_Bounds (Declaration_Node (E), Dimension, Dim_Index);
   end Do_Constrained_First_Last;

   function Do_Unconstrained_First_Last (The_Array  : Entity_Id;
                                         Dimension  : Positive;
                                         Source_Loc : Irep)
                                         return Dimension_Bounds
   is
      Raw_String  : constant String := Integer'Image (Dimension);
      Dim_String  : constant String := Raw_String (2 .. Raw_String'Last);
      Array_Name  : constant String := Unique_Name (The_Array);
      Prefix      : constant String := Array_Name & "___";
      First_Name  : constant String := Prefix & "first_" & Dim_String;
      Last_Name   : constant String := Prefix & "last_" & Dim_String;
      pragma Assert (Print_Msg ("The name is " & First_Name));
      First_Id    : constant Symbol_Id := Intern (First_Name);
      pragma Assert (Global_Symbol_Table.Contains (First_Id));
      Last_Id     : constant Symbol_Id := Intern (Last_Name);
      pragma Assert (Global_Symbol_Table.Contains (Last_Id));
      Attr_Type   : constant Irep :=
              Global_Symbol_Table (First_Id).SymType;
      First_Expr  : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Attr_Type,
           Range_Check     => False,
           Identifier      => First_Name);
      Last_Expr  : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           I_Type          => Attr_Type,
           Range_Check     => False,
           Identifier      => Last_Name);
   begin
      Put_Line ("An unconstrained array parameter");
      Put_Line ("The dimension string is:" & Dim_String);
      Put_Line ("The array name:" & Array_Name);
      return (First_Expr, Last_Expr);
   end Do_Unconstrained_First_Last;

   function Do_Array_Length (N : Node_Id) return Irep
   is
      --  It seems as though an N_Explicit_Drereference is placed in the tree
      --  even when the prefix of the Length attribute is an implicit
      --  dereference.
      --  Hence, implicit dereferences do not have to be seperately handled,
      --  they are handled as explicit dereferences.
      Array_Struct      : constant Irep := Do_Expression (Prefix (N));
   begin
      Put_Line ("******* Length");
      return Build_Array_Size (Array_Struct);
   end Do_Array_Length;

   function Do_Array_First (N : Node_Id) return Irep
   is
      --  It seems as though an N_Explicit_Drereference is placed in the tree
      --  even when the prefix of the Length attribute is an implicit
      --  dereference.
      --  Hence, implicit dereferences do not have to be seperately handled,
      --  they are handled as explicit dereferences.
   begin
      Put_Line ("******* First");
      return Get_First_Index (Do_Expression (Prefix (N)));
   end Do_Array_First;

   function Do_Array_Last (N : Node_Id) return Irep
   is
      --  It seems as though an N_Explicit_Drereference is placed in the tree
      --  even when the prefix of the Length attribute is an implicit
      --  dereference.
      --  Hence, implicit dereferences do not have to be seperately handled,
      --  they are handled as explicit dereferences.
   begin
      Put_Line ("******* Last");
      Print_Node_Briefly (Prefix (N));
      return Get_Last_Index (Do_Expression (Prefix (N)));
   end Do_Array_Last;

   ------------------------------
   -- Get_Array_Component_Type --
   ------------------------------

   function Get_Array_Component_Type (N : Node_Id) return Entity_Id is
      Ty : Entity_Id := Etype (N);
   begin
      while Ekind (Ty) = E_Array_Subtype loop
         Ty := Etype (Ty);
      end loop;
      return Component_Type (Ty);
   end Get_Array_Component_Type;

   -----------------------------------
   -- Make_Array_Object_From_Bounds --
   -----------------------------------
   procedure Make_Array_Object_From_Bounds (Block        : Irep;
                                            Array_Name   : String;
                                            Target_Type  : Entity_Id;
                                            Array_Length : Irep;
                                            Array_Bounds : Dimension_Bounds;
                                            Source_Loc   : Irep;
                                            The_Array    : out Irep)
   is
      Array_Id        : constant Symbol_Id := Intern (Array_Name);
      Comp_Etype      : constant Entity_Id :=
        Component_Type (Target_Type);
      Comp_Type_Pre   : constant Irep :=
        Do_Type_Reference (Comp_Etype);
      Comp_Type       : constant Irep :=
        (if Kind
           (Follow_Symbol_Type (Comp_Type_Pre, Global_Symbol_Table))
         = I_C_Enum_Type
         then
            Make_Unsignedbv_Type
           (ASVAT.Size_Model.Static_Size (Comp_Etype))
         else
            Comp_Type_Pre);
      Array_Type_Irep  : constant Irep :=
        Make_Array_Type
          (I_Subtype => Comp_Type,
           Size      => Array_Length);
      Array_Sym_Irep   : constant Irep :=
        Make_Symbol_Expr
          (Source_Location => Source_Loc,
           Identifier => Array_Name,
           I_Type => Array_Type_Irep);
      Decl             : constant Irep :=
        Make_Code_Decl
          (Symbol          => Array_Sym_Irep,
           Source_Location => Source_Loc);
      Array_Model_Size : constant Irep :=
        Make_Op_Mul
          (Rhs             => Typecast_If_Necessary
             (Expr           =>
                    ASVAT.Size_Model.Computed_Size (Comp_Etype),
              New_Type       => Index_T,
              A_Symbol_Table => Global_Symbol_Table),
           Lhs             => Array_Length,
           Source_Location => Source_Loc,
           Overflow_Check  => False,
           I_Type          => Index_T,
           Range_Check     => False);
   begin
        --  The_Array symbol can be updeated with a constrained
        --  length and the correct I_Array_Type.
      The_Array := Array_Sym_Irep;

      if not Global_Symbol_Table.Contains (Array_Id) then
         --  Declare the array companion variables and the array object
         Declare_First_Last_From_Bounds
           (Prefix     => Array_Name,
            Dimension  => "1",
            Index_Type => Etype (First_Index (Target_Type)),
            Bounds     => Array_Bounds,
            Block      => Block);

         Append_Op (Block, Decl);

         New_Object_Symbol_Entry
           (Object_Name       => Array_Id,
            Object_Type       => Array_Type_Irep,
            Object_Init_Value => Ireps.Empty,
            A_Symbol_Table    => Global_Symbol_Table);
         --  The model size of the object hast to be recorded.
         ASVAT.Size_Model.Set_Computed_Size
           (Id        => Array_Id,
            Size_Expr => Array_Model_Size);
      end if;
   end Make_Array_Object_From_Bounds;

   ------------------------------------------------
   -- Make_Constrained_Array_From_Initialization --
   ------------------------------------------------
   procedure Make_Constrained_Array_From_Initialization
     (Block        : Irep;
      Target_Type  : Entity_Id;
      Array_Name   : String;
      Init_Expr    : Node_Id;
      The_Array    : out Irep;
      Array_Bounds : out Static_And_Dynamic_Bounds)
   is
      Expr_Kind    : constant Node_Kind := Nkind (Init_Expr);
      Source_Loc   : constant Irep := Get_Source_Location (Init_Expr);
      Expr_Type    : constant Entity_Id := Etype (Init_Expr);
      Array_I_Type : constant Irep := Do_Type_Reference (Target_Type);
   begin
      --  The default array symbol is determined from the target type.
      --  If the target type is unconstrained and a constraint is determined
      --  from its initialization the array symbol will be updated once
      --  the constraints have been determined.
      The_Array := Make_Symbol_Expr
        (Source_Location => Source_Loc,
         I_Type          => Array_I_Type,
         Identifier      => Array_Name);

      Put_Line ("Make_Constrained_Array_From_Initialization");
      Put_Line (Array_Name);
      Put_Line (Node_Kind'Image (Nkind (Expr_Type)));
      Put_Line (Entity_Kind'Image (Ekind (Expr_Type)));
      Put_Line (Node_Kind'Image (Nkind (Init_Expr)));

      if Expr_Kind = N_Op_Concat then
         Put_Line ("A concatination");
         --  The array is initialized by a concatination.
         --  Determine the length of the concatination
         --  The resultant array from a concatination is 1 dimensional
         declare
            Cat_Array_Length : constant Irep :=
              Calculate_Concat_Length (Init_Expr);
            Cat_Array_Bounds : constant Dimension_Bounds :=
              Calculate_Concat_Bounds
                (Target_Type   => Target_Type,
                 Concat_Length => Cat_Array_Length);
         begin
            Put_Line ("The concatenation length is:");
            Print_Irep (Cat_Array_Length);
            Make_Array_Object_From_Bounds
              (Block        => Block,
               Array_Name   => Array_Name,
               Target_Type  => Target_Type,
               Array_Length => Cat_Array_Length,
               Array_Bounds => Cat_Array_Bounds,
               Source_Loc   => Source_Loc,
               The_Array    => The_Array);
               Array_Bounds :=
                 Static_And_Dynamic_Bounds'
                   (Is_Unconstrained  => False,
                    Has_Static_Bounds => False,
                    Low_Static        => 0,
                    High_Static       => 0,
                    Low_Dynamic       => Cat_Array_Bounds.Low,
                    High_Dynamic      => Cat_Array_Bounds.High);
         end;
      elsif Is_Constrained (Expr_Type) then
         Put_Line ("Is constrained");
         Print_Node_Briefly (Init_Expr);
         --  Add the array object to the symbol table and declare it.
         Array_Object_And_Friends
           (Array_Name => Array_Name,
            Array_Type => Expr_Type,
            Source_Loc => Source_Loc,
            Block      => Block);
               Array_Bounds :=
                 Multi_Dimension_Flat_Bounds (Init_Expr);
      elsif Expr_Kind = N_Function_Call then
         --  A call to a funcion which returns an unconstrained array.
         Report_Unhandled_Node_Empty
           (N        => Init_Expr,
            Fun_Name => "Make_Constrained_Array_From_Initialization",
            Message  => "Function calls returning unconstrained arrays " &
              "are unsupported.");
         --  For to allow coninuation of translation an unconstrained object
         --  is declared.
         Array_Object_And_Friends
           (Array_Name => Array_Name,
            Array_Type => Init_Expr,
            Source_Loc => Source_Loc,
            Block      => Block);
               Array_Bounds :=
                 Multi_Dimension_Flat_Bounds (Expr_Type);
      else
            Report_Unhandled_Node_Empty
              (Init_Expr,
               "Make_Constrained_Array_From_Initialization",
               "Unsupported unconstrained array initialization by " &
                 Node_Kind'Image (Nkind (Init_Expr)));
         --  For to allow coninuation of translation an unconstrained object
         --  is declared.
         Array_Object_And_Friends
           (Array_Name => Array_Name,
            Array_Type => Expr_Type,
            Source_Loc => Source_Loc,
            Block      => Block);
               Array_Bounds :=
                 Multi_Dimension_Flat_Bounds (Expr_Type);
      end if;
   end Make_Constrained_Array_From_Initialization;

   ---------------------------
   -- Make_Array_First_Expr --
   ---------------------------

   function Make_Array_First_Expr
     (Base_Type : Node_Id; Base_Irep : Irep) return Irep
   is
      First : constant Irep := Make_Member_Expr
         (Compound => Base_Irep,
          Source_Location => Get_Source_Location (Base_Type),
          Component_Number => 0,
          I_Type => CProver_Size_T,
          Component_Name => "first1");
   begin
      if not Is_Array_Type (Base_Type) then
         Report_Unhandled_Node_Empty (Base_Type, "Make_Array_First_Expr",
                                      "Base type not array type");
      end if;
      return First;
   end Make_Array_First_Expr;

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
      pragma Assert (Print_Msg ("Do_Slice Start"));
      pragma Assert (Print_Node (N));
      pragma Assert (Print_Node (Etype (N)));
      pragma Assert (Print_Node (First_Index (Etype (N))));
      pragma Assert (Print_Node (Etype (First_Index (Etype (N)))));
      pragma Assert (Print_Node
                     (Low_Bound
                          (Scalar_Range (Etype (First_Index (Etype (N)))))));
      pragma Assert (Print_Node
                     (High_Bound
                        (Scalar_Range (Etype (First_Index (Etype (N)))))));

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

      pragma Assert (Print_Irep_Func (Base_Irep));
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
      Put_Line ("Do_Slice Body Start");
      Print_Irep (Base_Irep);
      Print_Irep (Get_Type (Base_Irep));
      Print_Irep (Get_Size (Get_Type (Base_Irep)));
      Print_Irep (Get_Subtype (Get_Type (Base_Irep)));
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
   begin
      Put_Line ("Do_Indexed_Component");
      Print_Node_Briefly (The_Prefix);
      if Nkind (The_Prefix) = N_Slice then
         Put_Line ("A slice");
         Print_Node_Briefly (Prefix (The_Prefix));
         Print_Node_Briefly (Etype (Prefix (The_Prefix)));
      end if;

      Print_Node_Briefly (Prefix_Etype);
      if (if Nkind (Prefix_Etype) = N_Defining_Identifier then
             Get_Name_String (Chars (Etype (Etype (Prefix (N)))))
          elsif Is_Implicit_Deref then
             Get_Name_String (Chars (Designated_Type (Prefix_Etype)))
          else
             "")
        = "string"
      then
         return Report_Unhandled_Node_Irep (N, "Do_Expression",
                                            "Index of string unsupported");
      end if;

      declare
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

         Element_Type : constant Irep :=
           Do_Type_Reference (Component_Type (Array_Type));

         Source_Loc : constant Irep := Get_Source_Location (Base_Irep);

         Indexed_Data : constant Irep :=
           Make_Index_Expr
             (I_Array         => Base_Irep,
              Index           =>
                Typecast_If_Necessary
                  (Expr           => Calculate_Index_Offset
                     (Array_Node  => The_Prefix,
                      The_Indices => N),
                   New_Type       => Index_T,
                   A_Symbol_Table => Global_Symbol_Table),
              Source_Location => Source_Loc,
              I_Type          => Element_Type,
              Range_Check     => False);
      begin
         Put_Line ("Do_Indexed_Component_2");
         Print_Node_Subtree (Array_Type);
         Print_Irep (Calculate_Index_Offset (The_Prefix, N));
         Print_Irep (Element_Type);
         Print_Irep (Indexed_Data);

         return
           Indexed_Data;
--             Make_Dereference_Expr (Object          => Indexed_Data,
--                                    Source_Location => Source_Loc,
--                                    I_Type          => Element_Type);
      end;
   end Do_Indexed_Component;

   function Get_First_Index_Component (Array_Struct : Irep)
                                       return Irep
   is
      Array_Struct_Type : constant Irep :=
        Follow_Symbol_Type (Get_Type (Array_Struct), Global_Symbol_Table);
      Struct_Component : constant Irep_List :=
        Get_Component (Get_Components (Array_Struct_Type));
   begin
      return List_Element (Struct_Component, List_First (Struct_Component));
   end Get_First_Index_Component;

   function Get_Last_Index_Component (Array_Struct : Irep) return Irep
   is
      Array_Struct_Type : constant Irep :=
        Follow_Symbol_Type (Get_Type (Array_Struct), Global_Symbol_Table);
      Struct_Component : constant Irep_List :=
        Get_Component (Get_Components (Array_Struct_Type));
      Last_Cursor :  constant List_Cursor :=
        List_Next (Struct_Component, List_First (Struct_Component));
   begin
      return List_Element (Struct_Component, Last_Cursor);
   end Get_Last_Index_Component;

   function Get_Data_Component_From_Type (Array_Struct_Type : Irep)
                                          return Irep
   is
      Struct_Component : constant Irep_List :=
        Get_Component (Get_Components (Array_Struct_Type));
      Last_Cursor :  constant List_Cursor :=
        List_Next (Struct_Component,
                   List_Next (Struct_Component,
                     List_First (Struct_Component)));
   begin
      return List_Element (Struct_Component, Last_Cursor);
   end Get_Data_Component_From_Type;

   function Get_Data_Component (Array_Struct : Irep;
                                A_Symbol_Table : Symbol_Table)
                                return Irep
   is
      Array_Struct_Type : constant Irep :=
        Follow_Symbol_Type (Get_Type (Array_Struct), A_Symbol_Table);
   begin
      return Get_Data_Component_From_Type (Array_Struct_Type);
   end Get_Data_Component;

   function Get_First_Index (Array_Struct : Irep) return Irep
   is
      First_Index_Component : constant Irep :=
        Get_First_Index_Component (Array_Struct);
   begin
      return Make_Member_Expr (Compound         => Array_Struct,
                               Source_Location  => Internal_Source_Location,
                               Component_Number => 0,
                               I_Type           => CProver_Size_T,
                               Component_Name   =>
                                 Get_Name (First_Index_Component));
   end Get_First_Index;

   function Get_Last_Index (Array_Struct : Irep) return Irep
   is
      Last_Index_Component : constant Irep :=
        Get_Last_Index_Component (Array_Struct);
   begin
      return Make_Member_Expr (Compound         => Array_Struct,
                               Source_Location  => Internal_Source_Location,
                               Component_Number => 1,
                               I_Type           => CProver_Size_T,
                               Component_Name   =>
                                 Get_Name (Last_Index_Component));
   end Get_Last_Index;

   function Get_Data_Member (Array_Struct : Irep;
                             A_Symbol_Table : Symbol_Table)
                             return Irep
   is
      Data_Member : constant Irep :=
        Get_Data_Component (Array_Struct, A_Symbol_Table);
   begin
      return Make_Member_Expr (Compound         => Array_Struct,
                               Source_Location  => Internal_Source_Location,
                               Component_Number => 2,
                               I_Type           =>
                                 Get_Type (Data_Member),
                               Component_Name   =>
                                 Get_Name (Data_Member));
   end Get_Data_Member;

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

   function Build_Array_Size (First : Irep; Last : Irep; Idx_Type : Irep)
                              return Irep
   is
      Source_Loc : constant Irep := Get_Source_Location (First);
      Diff : constant Irep :=
        Make_Op_Sub (Rhs             => First,
                     Lhs             => Last,
                     Source_Location => Source_Loc,
                     Overflow_Check  => False,
                     I_Type          => Idx_Type);
      One : constant Irep :=
        Build_Index_Constant (Value      => 1,
                              Source_Loc => Source_Loc);
   begin
      return Make_Op_Add (Rhs             => One,
                          Lhs             => Diff,
                          Source_Location => Source_Loc,
                          Overflow_Check  => False,
                          I_Type          => Idx_Type);
   end Build_Array_Size;

   function Offset_Array_Data (Base : Irep; Offset : Irep) return Irep
   is
      Data_Member : constant Irep :=
        Get_Data_Member (Base, Global_Symbol_Table);
   begin
      return Make_Op_Add (Rhs             => Offset,
                          Lhs             => Data_Member,
                          Source_Location => Get_Source_Location (Base),
                          Overflow_Check  => False,
                          I_Type          => Get_Type (Data_Member));
   end Offset_Array_Data;

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

      Comp_Irep_Pre  : constant Irep :=
        Do_Type_Reference (Comp_Type);
      Comp_Irep      : constant Irep :=
        (if Kind (Follow_Symbol_Type (Comp_Irep_Pre, Global_Symbol_Table))
         = I_C_Enum_Type
         then
            Make_Unsignedbv_Type
           (ASVAT.Size_Model.Static_Size (Comp_Type))
         else
            Comp_Irep_Pre);

      --  Get the array zero based bounds.
      --  If the array is multi-dimmensional, the bounds are calculated
      --  by flattening th array into a one-dimensional eaquivalent.
      --  ASVAT represents multimensional arrays as equivalent one
      --  dimensional arrays.
      --  All goto arrays are index from 0, so the length is
      --  upper bound + 1.
      pragma Assert (Print_Msg ("From constrained_Array_Subtype"));
      pragma Assert (Print_Node (Array_Entity));
      pragma Assert (Print_Msg ("N_Has_Etype " &
                       Boolean'Image (Nkind (Array_Entity) in N_Has_Etype)));
      pragma Assert (Print_Msg ("Is_Array_Type " &
                       Boolean'Image (Is_Array_Type (Etype (Array_Entity)))));
      pragma Assert (Print_Node (Etype (Array_Entity)));

      Array_Bounds     : constant Static_And_Dynamic_Bounds :=
        Multi_Dimension_Flat_Bounds (Declaration);
      pragma Assert (Print_Msg ("After"));
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
      --  Set the ASVAT.Size_Model size for the array.
      ASVAT.Size_Model.Set_Computed_Size
        (Array_Entity, Array_Model_Size);
      Put_Line ("Make_Array_Subtype");
      Print_Node_Briefly (Declaration);
      Print_Node_Briefly (Array_Entity);
      Print_Node_Briefly (Comp_Type);
      Put_Line ("Has_Static_Bounds " &
        Boolean'Image (Array_Bounds.Has_Static_Bounds));
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
                 I_Type          => Make_Unsignedbv_Type (64),
                 Range_Check     => False,
                 Identifier      => Arr_Len);
         begin
            Put_Line ("******** dynamic range");
            Put_Line (Arr_Len);
            --  If the array subtype is an Itype then there is no point
            --  declaring the variable in the goto code as the type
            --  declaration is anonymous and does not appear in the
            --  goto code.
            --  Add the new variable to the symbol table and set its value
            --  to the computed length.
            New_Object_Symbol_Entry
              (Object_Name       => Arr_Len_Id,
               Object_Type       => Make_Unsignedbv_Type (64),
               Object_Init_Value => Make_Op_Typecast
                 (Op0             => Array_Length,
                  Source_Location => Source_Location,
                  I_Type          =>
                    Make_Unsignedbv_Type (64),
                  Range_Check     => False),
               A_Symbol_Table    => Global_Symbol_Table);
            Put_Line ("New var added to symbol table");

            Put_Line ("Done Make_Array_Subtype");
            --  Return the dynamic array type
            --  using the declared array length variable.
            return Make_Array_Type
              (I_Subtype => Comp_Irep,
               Size      => Arr_Len_Irep);
         end;
      end if;
      Put_Line ("Done Make_Array_Subtype");
      --  Return the array type using the static
      --  length of the array.
      return Make_Array_Type
        (I_Subtype => Comp_Irep,
         Size      => Array_Length);
   end Make_Constrained_Array_Subtype;

   function Make_Unconstrained_Array_Subtype (Declaration    : Node_Id;
                                              Component_Type : Entity_Id)
                                              return Irep
   is
      Sub_Pre : constant Irep :=
        Do_Type_Reference (Component_Type);
      Sub : constant Irep :=
        (if Kind (Follow_Symbol_Type (Sub_Pre, Global_Symbol_Table))
         = I_C_Enum_Type
         then
            Make_Unsignedbv_Type
           (ASVAT.Size_Model.Static_Size (Component_Type))
         else
            Sub_Pre);
      Nondet_Expr : constant Irep := Make_Side_Effect_Expr_Nondet
        (Source_Location => Get_Source_Location (Declaration),
         I_Type          => Index_T,
         Range_Check     => False);
   begin
      Put_Line ("Make_Unconstrained_Array_Subtype");
      Print_Node_Briefly (Declaration);
      Print_Irep (Sub);
      --  Set the ASVAT.Size_Model size for the unconstrained array to
      --  a nondet value.
      ASVAT.Size_Model.Set_Computed_Size
        (Defining_Identifier (Declaration), Nondet_Expr);
      Put_Line ("Computed_Size set");
      return Make_Array_Type
        (I_Subtype => Sub,
         Size      => Nondet_Expr);
   end Make_Unconstrained_Array_Subtype;

--        Ret_Components : constant Irep := Make_Struct_Union_Components;
--        Ret : constant Irep :=
--          Make_Struct_Type (Tag        => "unconstr_array",
--                            Components => Ret_Components);
--        Sub_Identifier : constant Node_Id :=
--          Subtype_Indication (Component_Definition (N));
--        Sub_Pre : constant Irep :=
--          Do_Type_Reference (Etype (Sub_Identifier));
--        Sub : constant Irep :=
--          (if Kind (Follow_Symbol_Type (Sub_Pre, Global_Symbol_Table))
--           = I_C_Enum_Type
--           then
--              Make_Signedbv_Type (32)
--           else
--              Sub_Pre);
--        Data_Type : constant Irep :=
--          Make_Pointer_Type (I_Subtype => Sub,
--                             Width     => Pointer_Type_Width);
--        Data_Member : constant Irep :=
--          Make_Struct_Component ("data", Data_Type);
--
--        Dimension_Iter : Node_Id :=
--          First ((if Nkind (N) = N_Unconstrained_Array_Definition then
--                     Subtype_Marks (N) else
--                     Discrete_Subtype_Definitions (N)));
--        Dimension_Number : Positive := 1;
--     begin
--
--   --  Define a structure with explicit first, last and data-pointer members
--
--        while Present (Dimension_Iter) loop
--           declare
--              Number_Str_Raw : constant String :=
--                Integer'Image (Dimension_Number);
--              Number_Str : constant String :=
--                Number_Str_Raw (2 .. Number_Str_Raw'Last);
--              First_Name : constant String := "first" & Number_Str;
--              Last_Name : constant String := "last" & Number_Str;
--              First_Comp : constant Irep :=
--                Make_Struct_Component (First_Name, CProver_Size_T);
--              Last_Comp : constant Irep :=
--                Make_Struct_Component (Last_Name, CProver_Size_T);
--           begin
--
--              Append_Component (Ret_Components, First_Comp);
--              Append_Component (Ret_Components, Last_Comp);
--
--           end;
--           Dimension_Number := Dimension_Number + 1;
--           Next (Dimension_Iter);
--        end loop;
--
--        Append_Component (Ret_Components, Data_Member);
--        return Ret;
--     end Do_Unconstrained_Array_Definition;

   procedure Pass_Array_Friends (Actual_Array : Entity_Id;  Args : Irep) is
--        Array_Name   : constant String := Unique_Name (Actual_Array);
      Array_Type   : constant Entity_Id := Etype (Actual_Array);
      Loc           : constant Irep := Get_Source_Location (Actual_Array);

      Index_Iter : Node_Id := First_Index (Array_Type);
   begin
      Put_Line ("Pass_Array_Friends");
      for Dimension in 1 .. Integer (Number_Dimensions (Array_Type)) loop
         pragma Assert (Present (Index_Iter));
         Print_Node_Briefly (Index_Iter);
         declare
            --  The actual array is either constrained or it is a formal
            --  parameter of a subprogram from which the call is made.
            Bounds : constant Dimension_Bounds :=
              (if Is_Formal (Actual_Array) then
                  Do_Unconstrained_First_Last (Actual_Array, Dimension, Loc)
               else
                  Do_Constrained_First_Last (Array_Type, Dimension));
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
   begin
      null;
   end Update_Array_From_Concatenation;

   procedure Update_Array_From_Slice
           (Block       : Irep;
            Slice       : Node_Id;
            Dest_Array  : Irep;
            Dest_Bounds : Static_And_Dynamic_Bounds)
   is
      pragma Assert (Print_Msg ("Update_Array_From slice - Slice prefix"));
      pragma Assert (Print_Node (Prefix (Slice)));
      Underlying_Array_Type : constant Entity_Id :=
        Get_Constrained_Subtype (Prefix (Slice));
      pragma Assert (Print_Msg ("After Prefix"));
      --  Do expression of a slice returns the array from which the
      --  slice is taken.
      pragma Assert (Print_Msg ("Update_Array_From slice - ExpressionSlice"));
      Underlying_Array : constant Irep := Do_Expression (Slice);
      pragma Assert (Print_Msg ("After Expression"));

      --  Get the slice bounds which are represented as offsets from the
      --  start of the array upon which the slice is defined.
      pragma Assert (Print_Msg ("Update_Array_From slice - Slice bounds"));
      Slice_Bounds : constant Static_And_Dynamic_Bounds :=
        Zero_Based_Bounds (Slice);
      pragma Assert (Print_Msg ("Update_Array_From slice - After bounds"));
   begin
      --  A check that the source and destination arrays have the
      --  same length may be required.
      Check_Equal_Array_Lengths (Block, Slice_Bounds, Dest_Bounds);
      Put_Line ("Copying from slice");
--        Put_Line ("Dest_Bounds");
--        Print_Irep (Dest_Bounds.Low_Dynamic);
--        Print_Irep (Dest_Bounds.High_Dynamic);
--        Print_Irep (Get_Lhs (Dest_Bounds.High_Dynamic));
--        Print_Irep (Get_Rhs (Dest_Bounds.High_Dynamic));
--        Print_Irep (Get_Lhs (Get_Lhs (Dest_Bounds.High_Dynamic)));
--        Print_Irep (Get_Lhs (Get_Lhs (Get_Lhs (Dest_Bounds.High_Dynamic))));
--        Print_Irep (Get_Rhs (Get_Lhs (Get_Lhs (Dest_Bounds.High_Dynamic))));
--
--        Put_Line ("Slice_Bounds");
--        Print_Irep (Slice_Bounds.Low_Dynamic);
--        Print_Irep (Slice_Bounds.High_Dynamic);
      Copy_Array
        (Block         => Block,
         Source_Type   => Underlying_Array_Type,
         Dest_Bounds   => Dest_Bounds,
         Source_Bounds => Slice_Bounds,
         Dest_Irep     => Dest_Array,
         Source_Irep   => Underlying_Array);
      Put_Line ("Copied from slice");
   end Update_Array_From_Slice;

end Arrays;
