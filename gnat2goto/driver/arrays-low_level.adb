with Nlists;                  use Nlists;
with Sem_Util;                use Sem_Util;
with Sem_Eval;                use Sem_Eval;
with Follow;                  use Follow;
with Tree_Walk;               use Tree_Walk;
with ASVAT.Size_Model;        use ASVAT.Size_Model;
with Treepr;                  use Treepr;
with Ada.Text_IO; use Ada.Text_IO;
package body Arrays.Low_Level is

   function Defining_Identifier (I : String; N : Node_Id) return Entity_Id;
   function Defining_Identifier (I : String; N : Node_Id) return Entity_Id is
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
         Put_Line ("Defining_Identifier - Arrays_Low_Level " & I);
         Put_Line ("Illegal node to Defining_Identifier");
         Print_Node_Briefly (N);
      end if;

      return Sinfo.Defining_Identifier (N);
   end Defining_Identifier;

   function Add_One_To_Index (Index : Static_And_Dynamic_Index)
                              return Static_And_Dynamic_Index is
      Result : Static_And_Dynamic_Index := Index;
   begin
      Add_One_To_Index (Result);
      return Result;
   end Add_One_To_Index;

   procedure Add_One_To_Index (Index : in out Static_And_Dynamic_Index) is
   begin
      if Index.Is_Static then
         Index.Static_Index := Index.Static_Index + Uint_1;
      else
         Index.Dynamic_Index := Inc_Index (Index.Dynamic_Index);
      end if;
   end Add_One_To_Index;

   function Sub_One_From_Index (Index : Static_And_Dynamic_Index)
                                return Static_And_Dynamic_Index is
      Result : Static_And_Dynamic_Index := Index;
   begin
      Sub_One_From_Index (Result);
      return Result;
   end Sub_One_From_Index;

   procedure Sub_One_From_Index (Index : in out Static_And_Dynamic_Index) is
   begin
      if Index.Is_Static then
         Index.Static_Index := Index.Static_Index - Uint_1;
      else
         Index.Dynamic_Index := Dec_Index (Index.Dynamic_Index);
      end if;
   end Sub_One_From_Index;

   function Add_To_Index (Index, Value_To_Add : Static_And_Dynamic_Index)
                          return Static_And_Dynamic_Index is
      Result : Static_And_Dynamic_Index := Index;
   begin
      Add_To_Index (Result, Value_To_Add);
      return Result;
   end Add_To_Index;

   procedure Add_To_Index (Index        : in out Static_And_Dynamic_Index;
                           Value_To_Add :        Static_And_Dynamic_Index) is
   begin
      if Index.Is_Static and Value_To_Add.Is_Static then
         Index.Static_Index := Index.Static_Index + Value_To_Add.Static_Index;
      else
         if Index.Is_Static then
            Index.Is_Static := False;
            Index.Dynamic_Index :=
              Integer_Constant_To_Expr
                (Value           => Index.Static_Index,
                 Expr_Type       => Index_T,
                 Source_Location => Internal_Source_Location);
         end if;

         Index.Dynamic_Index :=
           Make_Op_Add
             (Rhs             => Value_To_Add.Dynamic_Index,
              Lhs             => Index.Dynamic_Index,
              Source_Location => Internal_Source_Location,
              Overflow_Check  => False,
              I_Type          => Index_T,
              Range_Check     => False);
      end if;
   end Add_To_Index;

   function Get_Dynamic_Index (Index : Static_And_Dynamic_Index) return Irep
   is
     (if Index.Is_Static then
         Integer_Constant_To_Expr
        (Value           => Index.Static_Index,
         Expr_Type       => Index_T,
         Source_Location => Internal_Source_Location)
      else
         Index.Dynamic_Index
      );

   procedure Copy_Array_Dynamic
     (Block            : Irep;
      Source_Type      : Entity_Id;
      Dest_Low         : Irep;
      Dest_High        : Irep;
      Source_Low       : Irep;
      Source_High      : Irep;
      Dest_Irep        : Irep;
      Source_Irep      : Irep);

   procedure Copy_Array_Static
     (Block            : Irep;
      Source_Type      : Entity_Id;
      Dest_Low         : Int;
      Dest_High        : Int;
      Source_Low       : Int;
      Source_High      : Int;
      Dest_Irep        : Irep;
      Source_Irep      : Irep);

   ---------------------------
   -- All_Dimensions_Static --
   ---------------------------

   function All_Dimensions_Static (The_Array : Entity_Id) return Boolean is
      Next_Dim : Node_Id := First_Index (The_Array);
      Result : Boolean := True;
   begin
      while Present (Next_Dim) loop
         if not Is_OK_Static_Range (Get_Range (Next_Dim)) then
            Result := False;
            exit;
         end if;
         Next_Dim := Next_Index (Next_Dim);
      end loop;
      return Result;
   end All_Dimensions_Static;

   -------------------------------
   -- Assign_To_Array_Component --
   -------------------------------

   procedure Assign_To_Array_Component (Block      : Irep;
                                        The_Array  : Irep;
                                        Zero_Index : Irep;
                                        Value_Expr : Irep;
                                        I_Type     : Irep;
                                        Location   : Irep) is
   begin
      Append_Op
        (Block,
         Make_Code_Assign
           (Rhs             => Value_Expr,
            Lhs             =>
              Make_Index_Expr
                (I_Array         => The_Array,
                 Index           => Zero_Index,
                 Source_Location => Location,
                 I_Type          => I_Type,
                 Range_Check     => False),
            Source_Location => Location,
            I_Type          => I_Type,
            Range_Check     => False));
   end Assign_To_Array_Component;

   ----------------------------------------------
   -- Assign_Value_To_Dynamic_Array_Components --
   ----------------------------------------------

   procedure Assign_Value_To_Dynamic_Array_Components
     (Block            : Irep;
      The_Array        : Irep;
      Zero_Based_First : Irep;
      Zero_Based_Last  : Irep;
      Value_Expr       : Irep;
      I_Type           : Irep;
      Location         : Irep)
   is
      Loop_Var : constant Irep :=
        Fresh_Var_Symbol_Expr (Index_T, "loop_var");
      Loop_Body : constant Irep :=
        Make_Code_Block (Source_Location => Location);
   begin
      --  The body of the loop is just the assignment of the value expression
      --  to the indexed component.
      Assign_To_Array_Component
        (Block      => Loop_Body,
         The_Array  => The_Array,
         Zero_Index => Loop_Var,
         Value_Expr => Value_Expr,
         I_Type     => I_Type,
         Location   => Location);

      --  Now the loop can be constructed.
      Append_Op (Block,
                 Make_Simple_For_Loop
                   (Loop_Var        => Loop_Var,
                    First           => Zero_Based_First,
                    Last            => Zero_Based_Last,
                    Loop_Body       => Loop_Body,
                    Source_Location => Location));
   end Assign_Value_To_Dynamic_Array_Components;

   ---------------------------------------------
   -- Assign_Value_To_Static_Array_Components --
   ---------------------------------------------

   procedure Assign_Value_To_Static_Array_Components
     (Block            : Irep;
      The_Array        : Irep;
      Zero_Based_First : Int;
      Zero_Based_Last  : Int;
      Value_Expr       : Irep;
      I_Type           : Irep;
      Location         : Irep)
   is
   begin
      for I in Zero_Based_First .. Zero_Based_Last loop
         Assign_To_Array_Component
           (Block      => Block,
            The_Array  => The_Array,
            Zero_Index =>
              Integer_Constant_To_Expr
                (Value           => UI_From_Int (I),
                 Expr_Type       => Index_T,
                 Source_Location => Location),
            Value_Expr => Value_Expr,
            I_Type     => I_Type,
            Location   => Location);
      end loop;
   end Assign_Value_To_Static_Array_Components;

   -----------------------------
   -- Calculate_Concat_Bounds --
   -----------------------------

   function Calculate_Concat_Bounds
     (Target_Type   : Entity_Id;
      Concat_Length : Irep) return Dimension_Bounds is
   begin
      --  A concatination is always 1 dimensional.
      if Is_Constrained (Target_Type) then
         return Get_Bounds (First_Index (Target_Type));
      end if;

      declare
         Index      : constant Node_Id := First_Index (Target_Type);
         Index_Type : constant Entity_Id := Base_Type (Etype (Index));

         Type_Irep : constant Irep :=
           Do_Type_Reference (Index_Type);

         --  For unconstrained array type, a concatination takes the
         --  first value of the scalar index type.
         Lower_Bound  : constant Node_Id := Type_Low_Bound (Index_Type);
         Low_Irep     : constant Irep := Do_Expression (Lower_Bound);

         Low_Index    : constant Irep :=
           Typecast_If_Necessary
             (Expr           => Low_Irep,
              New_Type       => Index_T,
              A_Symbol_Table => Global_Symbol_Table);

         High_Index : constant Irep :=
           Make_Op_Sub
             (Rhs             => Index_T_One,
              Lhs             => Make_Op_Add
                (Rhs             => Concat_Length,
                 Lhs             => Low_Index,
                 Source_Location => Internal_Source_Location,
                 Overflow_Check  => False,
                 I_Type          => Index_T,
                 Range_Check     => False),
              Source_Location => Internal_Source_Location,
              Overflow_Check  => False,
              I_Type          => Index_T,
              Range_Check     => False);

         High_Irep : constant Irep :=
           Typecast_If_Necessary
             (Expr           => High_Index,
              New_Type       => Type_Irep,
              A_Symbol_Table => Global_Symbol_Table);
      begin
         return (Low_Irep, High_Irep);
      end;
   end Calculate_Concat_Bounds;

   -----------------------------
   -- Calculate_Concat_Length --
   -----------------------------

   function Calculate_Concat_Length (N : Node_Id) return Irep is

      procedure Calc_Length (N             : Node_Id;
                             Accum_Length  : in out Static_And_Dynamic_Index);

      procedure Calc_Length (N             : Node_Id;
                             Accum_Length  : in out Static_And_Dynamic_Index)
      is
      begin
         if Nkind (N) = N_Op_Concat then
            if Is_Component_Left_Opnd (N) then
               Add_One_To_Index (Accum_Length);
            else
               Calc_Length
                 (N            => Left_Opnd (N),
                  Accum_Length => Accum_Length);
            end if;
            if Is_Component_Right_Opnd (N) then
               Add_One_To_Index (Accum_Length);
            else
               Calc_Length
                 (N            => Right_Opnd (N),
                  Accum_Length => Accum_Length);
            end if;
         else
            declare
               --  In concatination the array can only have one dimension.
               Array_Type  : constant Entity_Id := Get_Constrained_Subtype (N);
               Array_Range : constant Node_Id := First_Index (Array_Type);
               Constrained : constant Boolean := Is_Constrained (Array_Type);
               Is_Static   : constant Boolean :=
                 Constrained and then Is_OK_Static_Range (Array_Range);
               Static_Len  : constant Uint :=
                 (if Is_Static then
                     Calculate_Static_Dimension_Length (Array_Range)
                  else
                     Uint_0);
               Dynamic_Len : constant Irep :=
                 (if not Is_Static and Constrained then
                     Calculate_Dimension_Length (Get_Bounds (Array_Range))
                  else
                     Ireps.Empty);
               Next_Length : constant Static_And_Dynamic_Index :=
                 Static_And_Dynamic_Index'
                   (Is_Static     => Is_Static,
                    Static_Index  => Static_Len,
                    Dynamic_Index => Dynamic_Len);
            begin
               if Constrained then
                  Add_To_Index (Index        => Accum_Length,
                                Value_To_Add => Next_Length);
               else
                  Report_Unhandled_Node_Empty
                    (N        => N,
                     Fun_Name => "Calculate_Concat_Length",
                     Message  => "Unconstrained array expressions in " &
                       "concatinations are unsupported");
               end if;
            end;
         end if;
      end Calc_Length;

      Accum_Length : Static_And_Dynamic_Index :=
        Static_And_Dynamic_Index'
          (Is_Static     => True,
           Static_Index  => Uint_0,
           Dynamic_Index => Ireps.Empty);
      Result : Irep;
   begin
      Calc_Length
        (N            => N,
         Accum_Length => Accum_Length);

      if Accum_Length.Is_Static then
         Result := Integer_Constant_To_Expr
           (Value           => Accum_Length.Static_Index,
            Expr_Type       => Index_T,
            Source_Location => Internal_Source_Location);
      else
         Result := Accum_Length.Dynamic_Index;
      end if;
      return Result;
   end Calculate_Concat_Length;

   --------------------------------
   -- Calculate_Dimension_Length --
   --------------------------------

   function Calculate_Dimension_Length (Bounds : Dimension_Bounds)
                                        return Irep is
      First_Val : constant Irep :=
        Typecast_If_Necessary
          (Expr           => Bounds.Low,
           New_Type       => Index_T,
           A_Symbol_Table => Global_Symbol_Table);
      Last_Val : constant Irep :=
        Typecast_If_Necessary
          (Expr           => Bounds.High,
           New_Type       => Index_T,
           A_Symbol_Table => Global_Symbol_Table);

      One : constant Irep :=
        Make_Constant_Expr
          (Source_Location => Internal_Source_Location,
           I_Type          => Index_T,
           Range_Check     => False,
           Value           => "1");

      Diff : constant Irep :=
        Make_Op_Sub
          (Rhs             => First_Val,
           Lhs             => Last_Val,
           Source_Location => Internal_Source_Location,
           Overflow_Check  => False,
           I_Type          => Index_T,
           Range_Check     => False);

      Length_Val : constant Irep :=
        Make_Op_Add
          (Rhs             => One,
           Lhs             => Diff,
           Source_Location => Internal_Source_Location,
           Overflow_Check  => False,
           I_Type          => Index_T,
           Range_Check     => False);
   begin
      return Length_Val;
   end Calculate_Dimension_Length;

   ----------------------------
   -- Calculate_Index_Offset --
   ----------------------------

   function Calculate_Index_Offset (Array_Node  : Node_Id;
                                    The_Indices : Node_Id) return Irep
   is
      Source_Location : constant Irep := Get_Source_Location (The_Indices);
      Array_Type  : constant Entity_Id := Etype (Array_Node);
      No_Of_Dims  : constant Positive :=
        Positive (Number_Dimensions (Array_Type));
      Index_Iter  : Node_Id := First (Expressions (The_Indices));
      Dim_Iter    : Node_Id := First_Index (Array_Type);
      Bounds_Iter : Dimension_Bounds :=
        Get_Dimension_Bounds (Array_Node, 1, Dim_Iter);
      Offset      : Irep :=
        Calculate_Zero_Offset (Index_Iter, Bounds_Iter);
   begin
      Put_Line ("Calculate_Index_Offset");
      Print_Node_Briefly (Array_Node);
      for I in 2 .. No_Of_Dims loop
         Index_Iter := Next (Index_Iter);
         Dim_Iter := Next_Index (Dim_Iter);
         Bounds_Iter := Get_Dimension_Bounds (Array_Node, I, Dim_Iter);
         Offset :=
           Make_Op_Add
             (Rhs             => Calculate_Zero_Offset
                (Index_Iter, Bounds_Iter),
              Lhs             => Make_Op_Mul
                (Rhs             => Offset,
                 Lhs             =>
                   Typecast_If_Necessary
                     (Expr           =>
                          Calculate_Dimension_Length (Bounds_Iter),
                      New_Type       => Index_T,
                      A_Symbol_Table => Global_Symbol_Table),
                 Source_Location => Source_Location,
                 Overflow_Check  => False,
                 I_Type          => Index_T,
                 Range_Check     => False),
              Source_Location => Source_Location,
              Overflow_Check  => False,
              I_Type          => Index_T,
              Range_Check     => False);
      end loop;
      return Offset;
   end Calculate_Index_Offset;

   -----------------------------------
   -- Calculate_Index_Offset_Static --
   -----------------------------------

   function Calculate_Index_Offset_Static (Array_Node  : Node_Id;
                                           The_Indices : Node_Id) return Int
   is
      Array_Type  : constant Entity_Id := Etype (Array_Node);
      No_Of_Dims  : constant Positive :=
        Positive (Number_Dimensions (Array_Type));
      Index_Iter  : Node_Id := First (Expressions (The_Indices));
      Dim_Iter    : Node_Id := First_Index (Array_Type);
      Offset      : Uint :=
        Expr_Value (Index_Iter) - Expr_Value (Low_Bound (Dim_Iter));
   begin
      for I in 2 .. No_Of_Dims loop
         Index_Iter := Next (Index_Iter);
         Dim_Iter := Next_Index (Dim_Iter);
         Offset :=
           (Calculate_Static_Dimension_Length (Get_Range (Dim_Iter)) *
             Offset) +
           (Expr_Value (Index_Iter) - Expr_Value (Low_Bound (Dim_Iter)));
      end loop;
      return UI_To_Int (Offset);
   end Calculate_Index_Offset_Static;

   ---------------------------------------
   -- Calculate_Static_Dimension_Length --
   ---------------------------------------

   function Calculate_Static_Dimension_Length (Dim_Range : Node_Id)
                                               return Uint
   is
     (Expr_Value (High_Bound (Dim_Range)) -
        Expr_Value (Low_Bound (Dim_Range)) + Uint_1);

   ---------------------------
   -- Calculate_Zero_Offset --
   ---------------------------

   function Calculate_Zero_Offset (Given_Index : Node_Id;
                                   Dim_Bounds  : Dimension_Bounds) return Irep
   is
      Index_Irep : constant Irep :=
        Typecast_If_Necessary
          (Expr           => Do_Expression (Given_Index),
           New_Type       => Index_T,
           A_Symbol_Table => Global_Symbol_Table);
   begin
      return
        Make_Op_Sub
          (Rhs             => Typecast_If_Necessary
             (Expr           => Dim_Bounds.Low,
              New_Type       => Index_T,
              A_Symbol_Table => Global_Symbol_Table),
           Lhs             => Typecast_If_Necessary
             (Expr           => Index_Irep,
              New_Type       => Index_T,
              A_Symbol_Table => Global_Symbol_Table),
           Source_Location => Get_Source_Location (Given_Index),
           Overflow_Check  => False,
           I_Type          => Index_T,
           Range_Check     => False);
   end Calculate_Zero_Offset;

   -------------------------------
   -- Check_Equal_Array_Lengths --
   -------------------------------

   procedure Check_Equal_Array_Lengths
     (Block         : Irep;
      Source_Bounds : Static_And_Dynamic_Bounds;
      Dest_Bounds   : Static_And_Dynamic_Bounds)
   is
      pragma Unreferenced (Block);
   begin
      if Source_Bounds.Has_Static_Bounds and Dest_Bounds.Has_Static_Bounds then
         declare
            Source_Length : constant Nat :=
              Source_Bounds.High_Static - Source_Bounds.Low_Static + 1;
            Dest_Length   : constant Nat :=
              Dest_Bounds.High_Static - Dest_Bounds.Low_Static + 1;
         begin
            if Source_Length /= Dest_Length then
               Put_Line ("Dynamic_Length check failed");
            end if;
         end;
      end if;
   end Check_Equal_Array_Lengths;

   ----------------
   -- Copy_Array --
   ----------------

   procedure Copy_Array (Block          : Irep;
                         Source_Type    : Entity_Id;
                         Dest_Bounds    : Static_And_Dynamic_Bounds;
                         Source_Bounds  : Static_And_Dynamic_Bounds;
                         Dest_Irep      : Irep;
                         Source_Irep    : Irep)
   is
      Static_Limit        : constant := 16;
   begin
      if (Dest_Bounds.Has_Static_Bounds and Source_Bounds.Has_Static_Bounds)
        and then
          Dest_Bounds.High_Static - Dest_Bounds.Low_Static + 1 <= Static_Limit
      then
         Copy_Array_Static
           (Block       => Block,
            Source_Type => Source_Type,
            Dest_Low    => Dest_Bounds.Low_Static,
            Dest_High   => Dest_Bounds.High_Static,
            Source_Low  => Source_Bounds.Low_Static,
            Source_High => Source_Bounds.High_Static,
            Dest_Irep   => Dest_Irep,
            Source_Irep => Source_Irep);
      else
         Copy_Array_Dynamic
           (Block       => Block,
            Source_Type => Source_Type,
            Dest_Low    => Dest_Bounds.Low_Dynamic,
            Dest_High   => Dest_Bounds.High_Dynamic,
            Source_Low  => Source_Bounds.Low_Dynamic,
            Source_High => Source_Bounds.High_Dynamic,
            Dest_Irep   => Dest_Irep,
            Source_Irep => Source_Irep);
      end if;
   end Copy_Array;

   ------------------------
   -- Copy_Array_Dynamic --
   ------------------------

   procedure Copy_Array_Dynamic
     (Block            : Irep;
      Source_Type      : Entity_Id;
      Dest_Low         : Irep;
      Dest_High        : Irep;
      Source_Low       : Irep;
      Source_High      : Irep;
      Dest_Irep        : Irep;
      Source_Irep      : Irep)
   is
      pragma Unreferenced (Source_High);  -- Used in precondition.
      Source_Location : constant Irep := Get_Source_Location (Dest_Irep);

      Component_Pre_Src  : constant Irep :=
        Do_Type_Reference (Component_Type (Source_Type));
      Component_Source   : constant Irep :=
        (if Kind (Follow_Symbol_Type (Component_Pre_Src,
         Global_Symbol_Table)) = I_C_Enum_Type
         then
            Make_Unsignedbv_Type
           (ASVAT.Size_Model.Static_Size
                (Component_Type (Source_Type)))
         else
            Component_Pre_Src);

      Component_Dest   : constant Irep := Get_Subtype (Get_Type (Dest_Irep));

      Loop_Var : constant Irep :=
        Fresh_Var_Symbol_Expr (Index_T, "loop_var");
      Loop_Body : constant Irep :=
        Make_Code_Block (Source_Location => Source_Location);

      Dest_Idx   : constant Irep :=
        Make_Op_Add
          (Rhs             => Dest_Low,
           Lhs             => Loop_Var,
           Source_Location => Source_Location,
           Overflow_Check  => False,
           I_Type          => Index_T,
           Range_Check     => False);
      Source_Idx : constant Irep :=
        Make_Op_Add
          (Rhs             => Source_Low,
           Lhs             => Loop_Var,
           Source_Location => Source_Location,
           Overflow_Check  => False,
           I_Type          => Index_T,
           Range_Check     => False);

      Loop_First : constant Irep := Dest_Low;
      Loop_Last  : constant Irep :=
        Make_Op_Sub
          (Rhs             => Dest_Low,
           Lhs             => Dest_High,
           Source_Location => Source_Location,
           Overflow_Check  => False,
           I_Type          => Index_T,
           Range_Check     => False);

      Indexed_Source   : constant Irep :=
        Make_Index_Expr
          (I_Array         => Source_Irep,
           Index           => Source_Idx,
           Source_Location => Source_Location,
           I_Type          => Component_Source,
           Range_Check     => False);

      Assign_Value     : constant Irep :=
        (if Component_Source = Component_Dest then
            Indexed_Source
         else
            Make_Op_Typecast
           (Op0             => Indexed_Source,
            Source_Location => Source_Location,
            I_Type          => Component_Dest,
            Range_Check     => False));
   begin
      --  The body of the loop is just the assignment of the indexed source
      --  element to the indexed destination element.
      Assign_To_Array_Component
        (Block      => Loop_Body,
         The_Array  => Dest_Irep,
         Zero_Index => Dest_Idx,
         Value_Expr => Assign_Value,
         I_Type     => Component_Dest,
         Location   => Source_Location);

      --  Now the loop can be constructed.
      Append_Op (Block,
                 Make_Simple_For_Loop
                   (Loop_Var        => Loop_Var,
                    First           => Loop_First,
                    Last            => Loop_Last,
                    Loop_Body       => Loop_Body,
                    Source_Location => Source_Location));
   end Copy_Array_Dynamic;

   -----------------------
   -- Copy_Array_Static --
   -----------------------

   procedure Copy_Array_Static
     (Block            : Irep;
      Source_Type      : Entity_Id;
      Dest_Low         : Int;
      Dest_High        : Int;
      Source_Low       : Int;
      Source_High      : Int;
      Dest_Irep        : Irep;
      Source_Irep      : Irep)
   is
      --  Currently Source_High is only referenced in the precondition.
      pragma Unreferenced (Source_High);
      Source_Location : constant Irep := Get_Source_Location (Dest_Irep);

      Component_Pre_Src  : constant Irep :=
        Do_Type_Reference (Component_Type (Source_Type));
      Component_Source   : constant Irep :=
        (if Kind (Follow_Symbol_Type (Component_Pre_Src,
         Global_Symbol_Table)) = I_C_Enum_Type
         then
            Make_Unsignedbv_Type
           (ASVAT.Size_Model.Static_Size
                (Component_Type (Source_Type)))
         else
            Component_Pre_Src);

      Component_Dest : constant Irep := Get_Subtype (Get_Type (Dest_Irep));
   begin
      for I in 0 .. Dest_High - Dest_Low  loop
         Assign_To_Array_Component
           (Block      => Block,
            The_Array  => Dest_Irep,
            Zero_Index =>
              Integer_Constant_To_Expr
                (Value           => UI_From_Int (I + Dest_Low),
                 Expr_Type       => Index_T,
                 Source_Location =>
                   Internal_Source_Location),
            Value_Expr =>
              Typecast_If_Necessary
                (Expr           =>
                     Make_Index_Expr
                   (I_Array         => Source_Irep,
                    Index           =>
                      Integer_Constant_To_Expr
                        (Value           => UI_From_Int (I + Source_Low),
                         Expr_Type       => Index_T,
                         Source_Location =>
                           Internal_Source_Location),
                    Source_Location =>
                      Internal_Source_Location,
                    I_Type          => Component_Source,
                    Range_Check     => False),
                 New_Type       => Component_Dest,
                 A_Symbol_Table => Global_Symbol_Table),
            I_Type     => Component_Dest,
            Location   => Source_Location);
      end loop;
   end Copy_Array_Static;

   -----------------
   -- Get_Bounds --
   ---------------

   function Get_Bounds (Index : Node_Id) return Dimension_Bounds
   is
      Bounds : constant Node_Id := Get_Range (Index);
      --  The front-end sometimes rewrites nodes giving them a different
      --  Goto requires the original identifier.
      Low  : constant Irep :=
        Do_Expression (Original_Node (Low_Bound (Bounds)));
      High : constant Irep :=
        Do_Expression (Original_Node (High_Bound (Bounds)));
   begin
      return (Low =>
                Typecast_If_Necessary
                  (Expr           => Low,
                   New_Type       => Index_T,
                   A_Symbol_Table => Global_Symbol_Table),
              High =>
                Typecast_If_Necessary
                  (Expr           => High,
                   New_Type       => Index_T,
                   A_Symbol_Table => Global_Symbol_Table));
   end Get_Bounds;

   -----------------------------
   -- Get_Constrained_Subtype --
   -----------------------------
   function Get_Constrained_Subtype (N : Node_Id) return Entity_Id is
      E_Type_N : constant Entity_Id := Etype (N);
   begin
      if Is_Constrained (E_Type_N) then
         return E_Type_N;
      end if;

      case Nkind (N) is
         when N_Identifier | N_Expanded_Name =>
            declare
               Dec_Node : constant Node_Id :=
                 Declaration_Node (Entity (N));
            begin
               pragma Assert (Has_Init_Expression (Dec_Node));
               return Get_Constrained_Subtype (Expression (Dec_Node));
            end;
         when N_Op_Concat =>
            --  There will not be a constrained subtype.
            --  return the unconstrained subtype.
            return E_Type_N;
         when N_Function_Call =>
            Report_Unhandled_Node_Empty
              (N        => N,
               Fun_Name => "Get_Constrained_Subtype",
               Message  => "Unsupported: " &
                 "functions returning unconstrained array types.");
            return E_Type_N;
         when N_Type_Conversion | N_Qualified_Expression =>
            return Get_Constrained_Subtype (Expression (N));
         when others =>
            Report_Unhandled_Node_Empty
              (N        => N,
               Fun_Name => "Get_Constrained_Subtype",
               Message  => "Unsuported unconstrained expression kind " &
                 Node_Kind'Image (Nkind (N)));
            return E_Type_N;
      end case;
   end Get_Constrained_Subtype;

   --------------------------
   -- Get_Dimension_Bounds --
   --------------------------

   function Get_Dimension_Bounds (N : Node_Id; Dim : Positive; Index : Node_Id)
                                  return Dimension_Bounds
   is
   begin
      Put_Line ("Get_Dimension_Bounds");
      Print_Node_Briefly (N);
      declare

         Source_Location : constant Irep := Get_Source_Location (N);
         Array_Type      : constant Entity_Id :=
           (case Nkind (N) is
               when N_Full_Type_Declaration | N_Subtype_Declaration =>
                  Defining_Identifier ("1", N),
               when N_Object_Declaration | N_Object_Renaming_Declaration =>
                  Etype (Defining_Identifier ("2", N)),
               when N_Defining_Identifier =>
              (if Is_Array_Type (N) then
                    N
               else
                  Etype (N)),
               when others =>
                  Etype (N));
      begin
         Print_Node_Briefly (Array_Type);
         Put_Line ("Constrained " &
                     Boolean'Image (Is_Constrained (Array_Type)));
         Put_Line ("Is_Constr_Subt_For_U_Nominal " &
                     Boolean'Image
                     (Is_Constr_Subt_For_U_Nominal (Array_Type)));
         if Is_Constrained (Array_Type) or else
           Is_Constr_Subt_For_U_Nominal (Array_Type) or else
           Nkind (Index) = N_Range
         then
            return Get_Bounds (Index);
         end if;

         --  The array is unconstrained but N must refer to an array object
         --  that has first and last auxillary variables declared for each
         --  dimension.
         Put_Line ("Is_Constrained " &
                     Boolean'Image (Is_Constrained (Array_Type)));
         Put_Line ("Is_Constr_Subt_For_U_Nominal " &
                     Boolean'Image
                     (Is_Constr_Subt_For_U_Nominal (Array_Type)));
         Print_Node_Briefly (N);
         declare
            Dim_String_Pre : constant String := Integer'Image (Dim);
            Dim_String     : constant String :=
              Dim_String_Pre (2 .. Dim_String_Pre'Last);

            pragma Assert (Nkind (N) in N_Object_Declaration
                             | N_Object_Renaming_Declaration
                               | N_Identifier
                                 | N_Expanded_Name
                                   | N_Defining_Identifier,
                           "Get_Dimension_Bounds - Not an object " &
                             Node_Kind'Image (Nkind (N)));

            Object_Entity : constant Entity_Id :=
              (case Nkind (N) is
                  when N_Defining_Identifier =>
                     N,
                  when N_Identifier | N_Expanded_Name =>
                     Entity (N),
                  when others =>
                     Defining_Identifier ("3", N));

            Index_Entity : constant Entity_Id :=
              (case Nkind (Index) is
                  when N_Defining_Identifier =>
                     Index,
                  when N_Identifier | N_Expanded_Name =>
                     Entity (Index),
                  when others =>
                     Defining_Identifier ("4", Index));

            Object_Name    : constant String := Unique_Name (Object_Entity);

            First_Var      : constant String :=
              Object_Name & First_Var_Str & Dim_String;
            Last_Var       : constant String :=
              Object_Name & Last_Var_Str & Dim_String;

            pragma Assert (Global_Symbol_Table.Contains (Intern (First_Var)),
                          First_Var);
            pragma Assert (Global_Symbol_Table.Contains (Intern (Last_Var)),
                          Last_Var);

            First_Sym      : constant Irep :=
              Make_Symbol_Expr
                (Source_Location => Source_Location,
                 I_Type          => Do_Type_Reference (Index_Entity),
                 Identifier      => First_Var);
            Last_Sym      : constant Irep :=
              Make_Symbol_Expr
                (Source_Location => Source_Location,
                 I_Type          => Do_Type_Reference (Index_Entity),
                 Identifier      => Last_Var);
         begin
            return Dimension_Bounds'
              (Low  => Typecast_If_Necessary
                 (Expr           => First_Sym,
                  New_Type       => Index_T,
                  A_Symbol_Table => Global_Symbol_Table),
               High => Typecast_If_Necessary
                 (Expr           => Last_Sym,
                  New_Type       => Index_T,
                  A_Symbol_Table => Global_Symbol_Table));
         end;
      end;
   end Get_Dimension_Bounds;

   ---------------
   -- Get_Range --
   ---------------

   function Get_Range (Index : Node_Id) return Node_Id is
     (if Nkind (Index) = N_Range
      then
      --  It is a range
         Index
      elsif Nkind (Index) = N_Subtype_Indication then
         --  It is a subtype with constraint
         Scalar_Range (Etype (Index))
      else
      --  It is a subtype mark
         Scalar_Range (Entity (Index)));

   --------------------------
   -- Make_Simple_For_Loop --
   --------------------------

   function Make_Simple_For_Loop (Loop_Var,  --  The loop variable
                                  First,     --  The initial value of loop var
                                  Last,      --  The final value of loop var
                                  Loop_Body, --  The body, using loop var
                                  Source_Location : Irep) return Irep
   is
      Loop_Init : constant Irep := Make_Code_Assign
        (Lhs => Loop_Var,
         Rhs => First,
         Source_Location => Source_Location);

      Loop_Cond : constant Irep :=
        Make_Op_Geq (Rhs             => Loop_Var,
                     Lhs             => Last,
                     Source_Location => Source_Location,
                     Overflow_Check  => False,
                     I_Type          => Make_Bool_Type);

      Loop_Inc : constant Irep := Inc_Index (Loop_Var);

      Loop_Post : constant Irep :=
        Make_Side_Effect_Expr_Assign
          (Lhs => Loop_Var,
           Rhs => Loop_Inc,
           Source_Location => Source_Location,
           I_Type => Get_Type (Loop_Var));

   begin
      return Make_Code_For
        (Loop_Body       => Loop_Body,
         Cond            => Loop_Cond,
         Init            => Loop_Init,
         Iter            => Loop_Post,
         Source_Location => Source_Location);
   end Make_Simple_For_Loop;

   ---------------------
   -- Make_Zero_Index --
   ---------------------

   function Make_Zero_Index (Index, First, Location : Irep) return Irep is
      Index_IT : constant Irep :=
        (if Get_Type (First) = Index_T then
              Index
         else
            Make_Op_Typecast
           (Op0             => Index,
            Source_Location => Location,
            I_Type          => Index_T));
      First_IT : constant Irep :=
        (if Get_Type (First) = Index_T then
              First
         else
            Make_Op_Typecast
           (Op0             => First,
            Source_Location => Location,
            I_Type          => Index_T));
   begin
      return
        Make_Op_Sub
          (Rhs             => First_IT,
           Lhs             => Index_IT,
           Source_Location => Location,
           I_Type          => Index_T);
   end Make_Zero_Index;

   function Make_Zero_Index (Index : Irep; First : Int; Location : Irep)
                             return Irep is
     (Make_Zero_Index
        (Index    => Index,
         First    => Integer_Constant_To_Expr
           (Value           => UI_From_Int (First),
            Expr_Type       => Index_T,
            Source_Location => Location),
         Location => Location));

   function Multi_Dimension_Flat_Bounds (S : String; Array_Node : Node_Id)
                                         return Static_And_Dynamic_Bounds
   is
      Source_Location : constant Irep := Get_Source_Location (Array_Node);
      --  The front-end ensures that the array has at least one dimension.
      Array_Node_Kind   : constant Node_Kind := Nkind (Array_Node);
      Array_Is_Object   : constant Boolean :=
        Array_Node_Kind in N_Object_Declaration |
                           N_Object_Renaming_Declaration |
                           N_Identifier |
                           N_Expanded_Name;

      Array_Type        : constant Entity_Id :=
        (case Nkind (Array_Node) is
            when N_Defining_Identifier =>
               Array_Node,
            when N_Full_Type_Declaration | N_Subtype_Declaration =>
               Defining_Identifier ("5", Array_Node),
            when N_Object_Declaration | N_Object_Renaming_Declaration =>
               Etype (Defining_Identifier ("6", Array_Node)),
            when N_Identifier | N_Expanded_Name =>
               Etype (Entity (Array_Node)),
            when others =>
               Etype (Array_Node));
   begin
      Put_Line ("Multi_Dimension_Flat_Bounds " & S);
      Print_Node_Briefly (Array_Node);
      --  Check to see if the array is  string literal
      --  Process and return if it is.
      if Ekind (Array_Type) = E_String_Literal_Subtype then
         declare
            Str_Lit_Length          : constant Uint :=
              String_Literal_Length (Array_Type);

            --  The goto array representing the string literal must
            --  index from 0.
            Char_Array_Low_Static    : constant Uint := Uint_0;

            --  As string literals are always stored by the front-end starting
            --  at index 1, the string length is the number of charaters in
            --  the string.  Since goto arrays are indexed from 0
            --  the high bound of the char array representing the string
            --  literal is the string literal lenght - 1.
            Char_Array_High_Static   : constant Uint :=
                  Str_Lit_Length - Uint_1;

            --  All goto arrays are indexed from 0
            Char_Array_Low_Irep      : constant Irep := Index_T_Zero;

            Char_Array_High_Irep   : constant Irep :=
              Integer_Constant_To_Expr
                (Value           => Char_Array_High_Static,
                 Expr_Type       => Index_T,
                 Source_Location => Source_Location);
         begin
            return Static_And_Dynamic_Bounds'
              (Is_Unconstrained  => False,
               Has_Static_Bounds => True,
               Low_Static        => UI_To_Int (Char_Array_Low_Static),
               High_Static       => UI_To_Int (Char_Array_High_Static),
               Low_Dynamic       => Char_Array_Low_Irep,
               High_Dynamic      => Char_Array_High_Irep);
         end;
      end if;

      --   Not a string literal.
      declare
         Constrained_Array : constant Boolean := Is_Constrained (Array_Type);
         Dimension_Number  : Positive := 1;
         Dimension_Iter    : Node_Id := First_Index (Array_Type);
         Dimension_Range   : Node_Id := Get_Range (Dimension_Iter);
         Var_Dim_Bounds    : Irep := Ireps.Empty;
         Static_Array_Size : Uint := Uint_0;

      begin
         if Constrained_Array or Array_Is_Object then
            if Constrained_Array and then Is_OK_Static_Range (Dimension_Range)
            then
               Static_Array_Size := Calculate_Static_Dimension_Length
                 (Dimension_Range);
            else
               --  Bounds are variable or it is an array object of an
               --  unconstrained subtype.
               Var_Dim_Bounds := Calculate_Dimension_Length
                 (Get_Dimension_Bounds
                    (Array_Node, Dimension_Number, Dimension_Iter));
            end if;

            --  Multidimensional arrays are converted into a a single
            --  dimension of an appropriate length.
            --  This needs to be considered when indexing into, or
            --  assigning aggregates to a multidimensional array.
            Dimension_Iter := Next (Dimension_Iter);
            while Present (Dimension_Iter) loop
               Dimension_Number := Dimension_Number + 1;
               Dimension_Range := Get_Range (Dimension_Iter);
               if Constrained_Array and then
                 Is_OK_Static_Range (Dimension_Range)
               then
                  Static_Array_Size := Static_Array_Size *
                    Calculate_Static_Dimension_Length (Dimension_Range);
               else
                  if Var_Dim_Bounds = Ireps.Empty then
                     Var_Dim_Bounds := Calculate_Dimension_Length
                       (Get_Dimension_Bounds
                          (Array_Node, Dimension_Number, Dimension_Iter));
                  else
                     Var_Dim_Bounds := Make_Op_Mul
                       (Rhs             => Calculate_Dimension_Length
                          (Get_Dimension_Bounds
                               (Array_Node, Dimension_Number, Dimension_Iter)),
                        Lhs             => Var_Dim_Bounds,
                        Source_Location => Internal_Source_Location,
                        Overflow_Check  => False,
                        I_Type          => Index_T,
                        Range_Check     => False);
                  end if;
               end if;
               Dimension_Iter := Next (Dimension_Iter);
            end loop;

            declare
               Has_Static_Bounds : constant Boolean :=
                 Var_Dim_Bounds = Ireps.Empty;

               Static_Size : constant Irep :=
                 (if Static_Array_Size /= Uint_0 then
                     Integer_Constant_To_Expr
                    (Value           => Static_Array_Size,
                     Expr_Type       => Index_T,
                     Source_Location => Internal_Source_Location)
                  else
                     Ireps.Empty);

               Array_Size : constant Irep :=
                 (if Var_Dim_Bounds = Ireps.Empty then
                     Static_Size
                  elsif Static_Array_Size /= Uint_0 then
                     Make_Op_Mul
                    (Rhs             => Static_Size,
                     Lhs             => Var_Dim_Bounds,
                     Source_Location => Internal_Source_Location,
                     Overflow_Check  => False,
                     I_Type          => Index_T,
                     Range_Check     => False)
                  else
                     Var_Dim_Bounds);
            begin
               --  Goto arrays are indexed from 0.
               return Static_And_Dynamic_Bounds'
                 (Is_Unconstrained  => False,
                  Has_Static_Bounds => Has_Static_Bounds,
                  Low_Static        => 0,
                  High_Static       => (if Has_Static_Bounds then
                                             UI_To_Int (Static_Array_Size - 1)
                                        else
                                           0),
                  Low_Dynamic       => Index_T_Zero,
                  High_Dynamic      =>
                    Make_Op_Sub
                      (Rhs             => Index_T_One,
                       Lhs             => Array_Size,
                       Source_Location => Internal_Source_Location,
                       Overflow_Check  => False,
                       I_Type          => Index_T,
                       Range_Check     => False));
            end;
         else
            declare
               Nondet_Index : constant Irep := Index_T_Zero;
--                   Make_Nondet_Expr
--                     (Source_Location => Internal_Source_Location,
--                      I_Type          => Index_T,
--                      Range_Check     => False);
            begin
               return Static_And_Dynamic_Bounds'
                 (Is_Unconstrained  => True,
                  Has_Static_Bounds => False,
                  Low_Static        => 0,
                  High_Static       => 0,
                  Low_Dynamic       => Nondet_Index,
                  High_Dynamic      => Nondet_Index);
            end;
         end if;
      end;
   end Multi_Dimension_Flat_Bounds;

   function Zero_Based_Bounds (The_Array : Node_Id)
                               return Static_And_Dynamic_Bounds
   is
      Array_Is_Slice    : constant Boolean := Nkind (The_Array) = N_Slice;
      Array_Type        : constant Entity_Id :=
        (if Array_Is_Slice then
              Get_Constrained_Subtype (Prefix (The_Array))
         else
            Get_Constrained_Subtype (Etype (The_Array)));

      Is_Unconstrained  : constant Boolean := not Is_Constrained (Array_Type);
   begin
      if Is_Unconstrained then
         return Static_And_Dynamic_Bounds'
           (Is_Unconstrained  => True,
            Has_Static_Bounds => False,
            Low_Static        => 0,
            High_Static       => 0,
            Low_Dynamic       => Ireps.Empty,
            High_Dynamic      => Ireps.Empty);
      elsif not Array_Is_Slice then
         --  The array may be multidimensional
         return Multi_Dimension_Flat_Bounds ("1", Array_Type);
      else
         --  It's a slice. A slice can only be one-dimensional.
         return Zero_Based_Slice_Bounds
           (The_Slice        => The_Array,
            Underlying_Array => Array_Type);
      end if;
   end Zero_Based_Bounds;

   function Zero_Based_Slice_Bounds (The_Slice        : Node_Id;
                                     Underlying_Array : Entity_Id)
                                     return Static_And_Dynamic_Bounds
   is
      Source_Location : constant Irep := Get_Source_Location (The_Slice);
      Slice_Range : constant Entity_Id := Discrete_Range (The_Slice);
      Has_Static_Bounds : constant Boolean :=
        All_Dimensions_Static (Underlying_Array) and
        Is_OK_Static_Range (Slice_Range);
   begin
      if Has_Static_Bounds then
         declare
            Slice_Low             : constant Uint :=
              Expr_Value (Low_Bound (Slice_Range));
            Slice_High            : constant Uint :=
              Expr_Value (High_Bound (Slice_Range));
            Underlying_Array_Low  : constant Uint :=
              Expr_Value (Low_Bound (First_Index (Underlying_Array)));
            Low_Static            : constant Nat :=
              UI_To_Int (Slice_Low - Underlying_Array_Low);
            High_Static           : constant Nat :=
              UI_To_Int (Slice_High - Underlying_Array_Low);
         begin
            return Static_And_Dynamic_Bounds'
              (Is_Unconstrained  => False,
               Has_Static_Bounds => True,
               Low_Static        => Low_Static,
               High_Static       => High_Static,
               Low_Dynamic       =>
                 Integer_Constant_To_Expr
                   (Value           => UI_From_Int (Low_Static),
                    Expr_Type       => Index_T,
                    Source_Location => Source_Location),
               High_Dynamic      =>
                 Integer_Constant_To_Expr
                   (Value           => UI_From_Int (High_Static),
                    Expr_Type       => Index_T,
                    Source_Location => Source_Location));
         end;
      else
         declare
            Slice_Low             : constant Irep :=
              Typecast_If_Necessary
                (Expr           =>
                   Do_Expression (Low_Bound (Slice_Range)),
                 New_Type       => Index_T,
                 A_Symbol_Table => Global_Symbol_Table);
            Slice_High            : constant Irep :=
              Typecast_If_Necessary
                (Expr           =>
                   Do_Expression (High_Bound (Slice_Range)),
                 New_Type       => Index_T,
                 A_Symbol_Table => Global_Symbol_Table);
            Underlying_Array_Low  : constant Irep :=
              Typecast_If_Necessary
                (Expr           =>
                   Do_Expression (Low_Bound (First_Index (Underlying_Array))),
                 New_Type       => Index_T,
                 A_Symbol_Table => Global_Symbol_Table);
            Low_Dynamic            : constant Irep :=
              Make_Op_Sub
                (Rhs             => Underlying_Array_Low,
                 Lhs             => Slice_Low,
                 Source_Location => Source_Location,
                 Overflow_Check  => False,
                 I_Type          => Index_T,
                 Range_Check     => False);
            High_Dynamic           : constant Irep :=
              Make_Op_Sub
                (Rhs             => Underlying_Array_Low,
                 Lhs             => Slice_High,
                 Source_Location => Source_Location,
                 Overflow_Check  => False,
                 I_Type          => Index_T,
                 Range_Check     => False);
         begin
            return Static_And_Dynamic_Bounds'
              (Is_Unconstrained  => False,
               Has_Static_Bounds => False,
               Low_Static        => 0,
               High_Static       => 0,
               Low_Dynamic       => Low_Dynamic,
               High_Dynamic      => High_Dynamic);
         end;
      end if;
   end Zero_Based_Slice_Bounds;

end Arrays.Low_Level;
