with Nlists;                  use Nlists;
with Sem_Eval;                use Sem_Eval;
with Tree_Walk;               use Tree_Walk;
package body Arrays.Low_Level is

   -------------------------------
   -- Assign_To_Array_Component --
   -------------------------------

   procedure Assign_To_Array_Component (Block      : Irep;
                                        The_Array  : Irep;
                                        Zero_Index : Irep;
                                        Value_Expr : Irep;
                                        I_Type     : Irep;
                                        Location   : Irep)
   is
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

--     procedure Assign_Value_To_Dynamic_Array_Components
--       (Block            : Irep;
--        The_Array        : Irep;
--        Zero_Based_First : Irep;
--        Zero_Based_Last  : Irep;
--        Value_Expr       : Irep;
--        I_Type           : Irep;
--        Location         : Irep)
--     is
--        Loop_Iter_Var : constant Irep :=
--          Fresh_Var_Symbol_Expr (Int64_T, "i");
--        Loop_Cond : constant Irep :=
--          Make_Op_Gt (Rhs             => Loop_Iter_Var,
--                      Lhs             => Zero_Based_Last,
--                      Source_Location => Location,
--                      Overflow_Check  => False,
--                      I_Type          => Make_Bool_Type);
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

   --------------------------------
   -- Calculate_Dimension_Length --
   --------------------------------

   function Calculate_Dimension_Length (Bounds : Dimension_Bounds)
                                        return Irep is
      First_Type : constant Irep := Get_Type (Bounds.Low);
      Last_Type  : constant Irep := Get_Type (Bounds.High);

      First_Val : constant Irep :=
        (if Kind (First_Type) /= I_Signedbv_Type or else
         Get_Width (First_Type) /= 64
         then
            Make_Op_Typecast
           (Op0             => Bounds.Low,
            Source_Location => Internal_Source_Location,
            I_Type          => Int64_T,
            Range_Check     => False)
         else
            Bounds.Low);
      Last_Val : constant Irep :=
        (if Kind (Last_Type) /= I_Signedbv_Type or else
         Get_Width (Last_Type) /= 64
         then
            Make_Op_Typecast
           (Op0             => Bounds.High,
            Source_Location => Internal_Source_Location,
            I_Type          => Int64_T,
            Range_Check     => False)
         else
            Bounds.High);

      One : constant Irep :=
        Make_Constant_Expr
          (Source_Location => Internal_Source_Location,
           I_Type          => Int64_T,
           Range_Check     => False,
           Value           => "1");

      Diff : constant Irep :=
        Make_Op_Sub
          (Rhs             => First_Val,
           Lhs             => Last_Val,
           Source_Location => Internal_Source_Location,
           Overflow_Check  => False,
           I_Type          => Int64_T,
           Range_Check     => False);

      Length_Val : constant Irep :=
        Make_Op_Add
          (Rhs             => One,
           Lhs             => Diff,
           Source_Location => Internal_Source_Location,
           Overflow_Check  => False,
           I_Type          => Int64_T,
           Range_Check     => False);
   begin
      return Length_Val;
   end Calculate_Dimension_Length;

   ----------------------------
   -- Calculate_Index_Offset --
   ----------------------------

   function Calculate_Index_Offset (The_Array   : Entity_Id;
                                    The_Indices : Node_Id) return Irep
   is
      Source_Location : constant Irep := Get_Source_Location (The_Indices);
      No_Of_Dims  : constant Positive :=
        Positive (Number_Dimensions (The_Array));
      Index_Iter  : Node_Id := First (Expressions (The_Indices));
      Dim_Iter    : Node_Id := First_Index (The_Array);
      Bounds_Iter : Dimension_Bounds := Get_Bounds (Dim_Iter);
      Offset      : Irep :=
        Calculate_Zero_Offset (Index_Iter, Bounds_Iter);
   begin
      for I in 2 .. No_Of_Dims loop
         Index_Iter := Next (Index_Iter);
         Dim_Iter := Next_Index (Dim_Iter);
         Bounds_Iter := Get_Bounds (Dim_Iter);
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
                      New_Type       => Int64_T,
                      A_Symbol_Table => Global_Symbol_Table),
                 Source_Location => Source_Location,
                 Overflow_Check  => False,
                 I_Type          => Int64_T,
                 Range_Check     => False),
              Source_Location => Source_Location,
              Overflow_Check  => False,
              I_Type          => Int64_T,
              Range_Check     => False);
      end loop;
      return Offset;
   end Calculate_Index_Offset;

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
           New_Type       => Int64_T,
           A_Symbol_Table => Global_Symbol_Table);
   begin
      return
        Make_Op_Sub
          (Rhs             => Typecast_If_Necessary
             (Expr           => Dim_Bounds.Low,
              New_Type       => Int64_T,
              A_Symbol_Table => Global_Symbol_Table),
           Lhs             => Typecast_If_Necessary
             (Expr           => Index_Irep,
              New_Type       => Int64_T,
              A_Symbol_Table => Global_Symbol_Table),
           Source_Location => Get_Source_Location (Given_Index),
           Overflow_Check  => False,
           I_Type          => Int64_T,
           Range_Check     => False);
   end Calculate_Zero_Offset;

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
      return (Low => Low, High => High);
   end Get_Bounds;

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

   ---------------------
   -- Make_Zero_Index --
   ---------------------

   function Make_Zero_Index (Index, First, Location : Irep) return Irep is
     (Make_Op_Sub
        (Rhs             => First,
         Lhs             =>
            Typecast_If_Necessary
           (Expr           => Index,
            New_Type       => Int64_T,
            A_Symbol_Table =>
               Global_Symbol_Table),
         Source_Location => Location,
         Overflow_Check  => False,
         I_Type          => Int64_T,
         Range_Check     => False));

   function Make_Zero_Index (Index : Irep; First : Int; Location : Irep)
                             return Irep is
     (Make_Zero_Index
        (Index    => Index,
         First    => Integer_Constant_To_Expr
           (Value           => UI_From_Int (First),
            Expr_Type       => Int64_T,
            Source_Location => Location),
         Location => Location));

end Arrays.Low_Level;
