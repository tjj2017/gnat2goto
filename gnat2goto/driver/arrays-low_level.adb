with Nlists;                  use Nlists;
with Sem_Eval;                use Sem_Eval;
with Tree_Walk;               use Tree_Walk;
with Ada.Text_IO; use Ada.Text_IO;
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
        Fresh_Var_Symbol_Expr (Int64_T, "loop_var");
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

      Put_Line ("££££££££££££ Making Loop");
      Print_Irep (Zero_Based_First);
      Print_Irep (Zero_Based_Last);
      Print_Irep (Value_Expr);
      Print_Irep (Loop_Body);
      Print_Irep (Block);
      Print_Irep (Make_Simple_For_Loop
                   (Loop_Var        => Loop_Var,
                    First           => Zero_Based_First,
                    Last            => Zero_Based_Last,
                    Loop_Body       => Loop_Body,
                    Source_Location => Location));

      --  Now the loop can be constructed.
      Append_Op (Block,
                 Make_Simple_For_Loop
                   (Loop_Var        => Loop_Var,
                    First           => Zero_Based_First,
                    Last            => Zero_Based_Last,
                    Loop_Body       => Loop_Body,
                    Source_Location => Location));
      Put_Line ("Assign_To_Dyn");
      Print_Irep (Block);
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
                 Expr_Type       => Int64_T,
                 Source_Location => Location),
            Value_Expr => Value_Expr,
            I_Type     => I_Type,
            Location   => Location);
      end loop;
   end Assign_Value_To_Static_Array_Components;

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
         Rhs => Typecast_If_Necessary
           (First,
            Get_Type (Loop_Var),
            Global_Symbol_Table),
         Source_Location => Source_Location);

      Loop_Cond : constant Irep :=
        Make_Op_Geq (Rhs             => Loop_Var,
                     Lhs             => Last,
                     Source_Location => Source_Location,
                     Overflow_Check  => False,
                     I_Type          => Make_Bool_Type);

      Loop_Inc : constant Irep :=
        Make_Op_Add
          (Lhs => Loop_Var,
           Rhs =>  Integer_Constant_To_Expr
             (Value           => Uint_1,
              Expr_Type       => Int64_T,
              Source_Location => Internal_Source_Location),
           I_Type => Get_Type (Loop_Var),
           Source_Location => Internal_Source_Location);

      Loop_Post : constant Irep :=
        Make_Side_Effect_Expr_Assign
          (Lhs => Loop_Var,
           Rhs => Loop_Inc,
           Source_Location => Internal_Source_Location,
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
     (Make_Op_Sub
        (Rhs             =>
              Typecast_If_Necessary
           (Expr           => First,
            New_Type       => Int64_T,
            A_Symbol_Table => Global_Symbol_Table),
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
