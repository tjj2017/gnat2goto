with Nlists;                  use Nlists;
with Sem_Eval;                use Sem_Eval;
with Follow;                  use Follow;
with Tree_Walk;               use Tree_Walk;
with ASVAT.Size_Model;        use ASVAT.Size_Model;
with Treepr;                  use Treepr;
with Ada.Text_IO; use Ada.Text_IO;
package body Arrays.Low_Level is

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

      Put_Line ("������������ Making Loop");
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
      procedure Add_One (Is_Static      : Boolean;
                         Static_Length  : in out Uint;
                         Dynamic_Length : in out Irep);

      procedure Calc_Length (N              : Node_Id;
                             Is_Static      : in out Boolean;
                             Static_Length  : in out Uint;
                             Dynamic_Length : in out Irep);

      procedure Add_One (Is_Static      : Boolean;
                         Static_Length  : in out Uint;
                         Dynamic_Length : in out Irep)
      is
      begin
         if Is_Static then
            Static_Length := Static_Length + Uint_1;
         else
            Dynamic_Length := Inc_Index (Dynamic_Length);
         end if;
      end Add_One;

      procedure Calc_Length (N              : Node_Id;
                             Is_Static      : in out Boolean;
                             Static_Length  : in out Uint;
                             Dynamic_Length : in out Irep) is
      begin
         if Nkind (N) = N_Op_Concat then
            if Is_Component_Left_Opnd (N) then
               Add_One (Is_Static, Static_Length, Dynamic_Length);
            else
               Calc_Length
                 (N              => Left_Opnd (N),
                  Is_Static      => Is_Static,
                  Static_Length  => Static_Length,
                  Dynamic_Length => Dynamic_Length);
            end if;
            if Is_Component_Right_Opnd (N) then
               Add_One (Is_Static, Static_Length, Dynamic_Length);
            else
               Calc_Length
                 (N              => Right_Opnd (N),
                  Is_Static      => Is_Static,
                  Static_Length  => Static_Length,
                  Dynamic_Length => Dynamic_Length);
            end if;
         else
            declare
               --  The array can only have one dimension.
               Array_Type  : constant Entity_Id := Get_Constrained_Subtype (N);
               Array_Range : constant Node_Id := First_Index (Array_Type);
            begin
               if Is_Constrained (Array_Type) then
                  if Is_Static and then Is_OK_Static_Range (Array_Range) then
                     Static_Length := Static_Length +
                       Calculate_Static_Dimension_Length (Array_Range);
                  else
                     declare
                        Bounds : constant Dimension_Bounds :=
                          Get_Bounds (Array_Range);
                     begin
                        if Is_Static then
                           Is_Static := False;
                           Dynamic_Length :=
                             Integer_Constant_To_Expr
                               (Value           => Static_Length,
                                Expr_Type       => Index_T,
                                Source_Location => Internal_Source_Location);
                        end if;

                        Dynamic_Length :=
                          Make_Op_Add
                            (Rhs             =>
                               Calculate_Dimension_Length (Bounds),
                             Lhs             => Dynamic_Length,
                             Source_Location => Internal_Source_Location,
                             Overflow_Check  => False,
                             I_Type          => Index_T,
                             Range_Check     => False);
                     end;
                  end if;
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

      Is_Static      : Boolean := True;
      Static_Length  : Uint := Uint_0;
      Dynamic_Length : Irep := Ireps.Empty;
      Result : Irep;
   begin
      Put_Line ("Calculate_Cocat_Length");
      Calc_Length
        (N              => N,
         Is_Static      => Is_Static,
         Static_Length  => Static_Length,
         Dynamic_Length => Dynamic_Length);
      if Is_Static then
         Put_Line ("Result is static: " &
                  Int'Image (UI_To_Int (Static_Length)));
         Result := Integer_Constant_To_Expr
           (Value           => Static_Length,
            Expr_Type       => Index_T,
            Source_Location => Internal_Source_Location);
      else
         Put_Line ("The_Result is dynamic:");
         Print_Irep (Dynamic_Length);
         Result := Dynamic_Length;
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
         Put_Line ("Static length check");
         declare
            Source_Length : constant Nat :=
              Source_Bounds.High_Static - Source_Bounds.Low_Static + 1;
            Dest_Length   : constant Nat :=
              Dest_Bounds.High_Static - Dest_Bounds.Low_Static + 1;
         begin
            if Source_Length /= Dest_Length then
               Put_Line ("??? Length check failed");
            end if;
         end;
      else
         Put_Line ("Dynamic length check");
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
      Static_Limit : constant := 16;
   begin
      if (Dest_Bounds.Has_Static_Bounds and Source_Bounds.Has_Static_Bounds)
        and then
          Dest_Bounds.High_Static - Dest_Bounds.Low_Static + 1 <= Static_Limit
      then
         Put_Line ("About to copy static");
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
         Put_Line ("About to copy dynamic");
         Print_Irep (Dest_Irep);
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
      Put_Line ("assign_to_array_component");
      Put_Line ("destination");
      Print_Irep (Dest_Irep);
      Print_Irep (Get_Type (Dest_Irep));
      Print_Irep (Get_Subtype (Get_Type (Dest_Irep)));
      Put_Line ("assign_to_array_component");
      Put_Line ("Source");
      Print_Irep (Source_Irep);
      Print_Irep (Get_Type (Source_Irep));
      Print_Irep (Get_Subtype (Get_Type (Source_Irep)));
      Print_Irep (Assign_Value);
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

      Component_Dest : constant Irep := Get_Subtype (Dest_Irep);
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
      return (Low => Low, High => High);
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

   function Multi_Dimension_Flat_Bounds (Array_Type : Entity_Id)
                                         return Static_And_Dynamic_Bounds
   is
      --  The front-end ensures that the array has at least one dimension.
      Dimension_Number  : Positive := 1;
      Dimension_Iter    : Node_Id := First_Index (Array_Type);
      Dimension_Range   : Node_Id := Get_Range (Dimension_Iter);
      Var_Dim_Bounds    : Irep := Ireps.Empty;
      Static_Array_Size : Uint := Uint_0;

   begin
      Put_Line ("Is constrained "
                & Boolean'Image (Is_Constrained (Array_Type)));
      Print_Node_Briefly (Array_Type);
      Print_Node_Briefly (Dimension_Range);
      if Is_Constrained (Array_Type) then
         if Is_OK_Static_Range (Dimension_Range) then
            Put_Line ("Ok static range");
            Static_Array_Size := Calculate_Static_Dimension_Length
              (Dimension_Range);
            Put_Line ("The first dimension size is " &
                        Int'Image (UI_To_Int (Static_Array_Size)));
         else
            Put_Line ("Variable bounds");
            Var_Dim_Bounds := Calculate_Dimension_Length
              (Get_Bounds (Dimension_Iter));
         end if;

         Put_Line ("Now for multi-dimensional");
         --  Multidimensional arrays are converted into a a single
         --  dimension of an appropriate length.
         --  This needs to be considered when indexing into, or
         --  assigning aggregates to a multidimensional array.
         Dimension_Iter := Next (Dimension_Iter);
         while Present (Dimension_Iter) loop
            Dimension_Number := Dimension_Number + 1;
            Dimension_Range := Get_Range (Dimension_Iter);
            if Is_OK_Static_Range (Dimension_Range) then
               Static_Array_Size := Static_Array_Size *
                 Calculate_Static_Dimension_Length (Dimension_Range);
            else
               if Var_Dim_Bounds = Ireps.Empty then
                  Var_Dim_Bounds := Calculate_Dimension_Length
                    (Get_Bounds (Dimension_Iter));
               else
                  Var_Dim_Bounds := Make_Op_Mul
                    (Rhs             => Calculate_Dimension_Length
                       (Get_Bounds (Dimension_Iter)),
                     Lhs             => Var_Dim_Bounds,
                     Source_Location => Internal_Source_Location,
                     Overflow_Check  => False,
                     I_Type          => Index_T,
                     Range_Check     => False);
               end if;
            end if;
            Dimension_Iter := Next (Dimension_Iter);
         end loop;

         Put_Line ("After loop");
         if Static_Array_Size = Uint_0 then
            Put_Line ("Static array size 0");
         else
            Put_Line ("Static array size " &
                        Int'Image (UI_To_Int (Static_Array_Size)));
         end if;
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
         Put_Line ("Is unconstrained array");
         declare
            Nondet_Index : constant Irep :=
              Make_Nondet_Expr
                (Source_Location => Internal_Source_Location,
                 I_Type          => Index_T,
                 Range_Check     => False);
         begin
            Put_Line ("About to return");
            return Static_And_Dynamic_Bounds'
              (Is_Unconstrained  => True,
               Has_Static_Bounds => False,
               Low_Static        => 0,
               High_Static       => 0,
               Low_Dynamic       => Nondet_Index,
               High_Dynamic      => Nondet_Index);
         end;
      end if;
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
      Put_Line ("Zero based bounds " &
                  Boolean'Image (Is_Unconstrained));
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
         return Multi_Dimension_Flat_Bounds (Array_Type);
      else
         --  It's a slice. A slice can only be one-dimensional.
         Put_Line ("Its a slice");
         Print_Node_Briefly (The_Array);
         Print_Node_Briefly (Etype (The_Array));
         Put_Line ("Calling Zero_Based_Slice_Bounds");
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
      Put_Line ("Zero_Based_Slice_Bounds " &
                  Boolean'Image (Has_Static_Bounds));
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
         Put_Line ("Zero_Based_Slice_Bounds - dynamic bounds");
         Print_Node_Subtree (Slice_Range);
         Print_Node_Briefly (First_Index (Underlying_Array));
         Put_Line ("Low bound slice");
         Print_Node_Briefly (Low_Bound (Slice_Range));
         Put_Line ("High bound slice");
         Print_Node_Subtree (High_Bound (Slice_Range));
         Put_Line ("Low bound underlying");
         Print_Node_Briefly (Low_Bound (First_Index (Underlying_Array)));
         Put_Line ("About to declare");
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
            Put_Line ("The slice bounds");
            Print_Irep (Slice_Low);
            Print_Irep (Get_Op0 (Slice_Low));
            Print_Irep (Slice_High);
            Print_Irep (Get_Op0 (Slice_High));
            Put_Line ("The underlying bounds");
            Print_Irep (Underlying_Array_Low);
            Print_Irep (Get_Op0 (Underlying_Array_Low));
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
