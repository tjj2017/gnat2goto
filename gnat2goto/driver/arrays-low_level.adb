with Nlists;                  use Nlists;
with Sem_Eval;                use Sem_Eval;
with Follow;                  use Follow;
with Tree_Walk;               use Tree_Walk;
with ASVAT.Size_Model;        use ASVAT.Size_Model;
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

   ------------------------------
   -- Calculate_Concat_Length --
   -----------------------------

   function Calculate_Concat_Length (N : Node_Id) return Irep is
      procedure Add_One (Is_Static      : Boolean;
                         Static_Length  : in out Uint;
                         Dynamic_Length : in out Irep);

      procedure Calc_Length (N             : Node_Id;
                             Is_Static     : in out Boolean;
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

      procedure Calc_Length (N             : Node_Id;
                             Is_Static     : in out Boolean;
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

   ------------------------
   -- Copy_Array_Dynamic --
   ------------------------

   procedure Copy_Array_Dynamic
     (Block            : Irep;
      Destination_Type : Entity_Id;
      Source_Type      : Entity_Id;
      Zero_Based_High  : Irep;
      Dest_Irep        : Irep;
      Source_Irep      : Irep)
   is
      --  All goto arrays index from 0.
      Low_Idx  : constant Irep := Index_T_Zero;
      --  The length ot the destination and source arrays should be the same.
      High_Idx : constant Irep :=
        Typecast_If_Necessary
          (Expr           => Zero_Based_High,
           New_Type       => Index_T,
           A_Symbol_Table => Global_Symbol_Table);
   begin
      Copy_Array_With_Offset_Dynamic
        (Block            => Block,
         Destination_Type => Destination_Type,
         Source_Type      => Source_Type,
         Dest_Low         => Low_Idx,
         Dest_High        => High_Idx,
         Source_Low       => Low_Idx,
         Source_High      => High_Idx,
         Dest_Irep        => Dest_Irep,
         Source_Irep      => Source_Irep);
   end Copy_Array_Dynamic;

   -----------------------
   -- Copy_Array_Static --
   -----------------------

   procedure Copy_Array_Static
     (Block            : Irep;
      Destination_Type : Entity_Id;
      Source_Type      : Entity_Id;
      Zero_Based_High  : Int;
      Dest_Irep        : Irep;
      Source_Irep      : Irep) is
   begin
      Copy_Array_With_Offset_Static
        (Block            => Block,
         Destination_Type => Destination_Type,
         Source_Type      => Source_Type,
         Dest_Low         => 0,
         Dest_High        => Zero_Based_High,
         Source_Low       => 0,
         Source_High      => Zero_Based_High,
         Dest_Irep        => Dest_Irep,
         Source_Irep      => Source_Irep);
   end Copy_Array_Static;

   ------------------------------------
   -- Copy_Array_With_Offset_Dynamic --
   ------------------------------------

   procedure Copy_Array_With_Offset_Dynamic
     (Block            : Irep;
      Destination_Type : Entity_Id;
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

      Component_Pre_Dest : constant Irep :=
        Do_Type_Reference (Component_Type (Destination_Type));
      Component_Dest     : constant Irep :=
        (if Kind (Follow_Symbol_Type (Component_Pre_Dest,
         Global_Symbol_Table)) = I_C_Enum_Type
         then
            Make_Unsignedbv_Type
           (ASVAT.Size_Model.Static_Size
                (Component_Type (Destination_Type)))
         else
            Component_Pre_Dest);

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

      Loop_First : constant Irep := Index_T_Zero;
      Loop_Last  : constant Irep :=
        Make_Op_Sub
          (Rhs             => Dest_Low,
           Lhs             => Dest_High,
           Source_Location => Internal_Source_Location,
           Overflow_Check  => False,
           I_Type          => Index_T,
           Range_Check     => False);
   begin
      --  The body of the loop is just the assignment of the indexed source
      --  element to the indexed destination element.
      Assign_To_Array_Component
        (Block      => Loop_Body,
         The_Array  => Dest_Irep,
         Zero_Index => Dest_Idx,
         Value_Expr =>
           Typecast_If_Necessary
             (Expr           =>
                  Make_Index_Expr
                (I_Array         => Source_Irep,
                 Index           => Source_Idx,
                 Source_Location => Internal_Source_Location,
                 I_Type          => Component_Source,
                 Range_Check     => False),
              New_Type       => Component_Dest,
              A_Symbol_Table => Global_Symbol_Table),
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
   end Copy_Array_With_Offset_Dynamic;

   -----------------------------------
   -- Copy_Array_With_Offset_Static --
   -----------------------------------

   procedure Copy_Array_With_Offset_Static
     (Block            : Irep;
      Destination_Type : Entity_Id;
      Source_Type      : Entity_Id;
      Dest_Low         : Int;
      Dest_High        : Int;
      Source_Low       : Int;
      Source_High      : Int;
      Dest_Irep        : Irep;
      Source_Irep      : Irep)
   is
      pragma Unreferenced (Source_High);  -- Used in precondition.
      Source_Location : constant Irep := Get_Source_Location (Dest_Irep);

      Component_Pre_Dest : constant Irep :=
        Do_Type_Reference (Component_Type (Destination_Type));
      Component_Dest     : constant Irep :=
        (if Kind (Follow_Symbol_Type (Component_Pre_Dest,
         Global_Symbol_Table)) = I_C_Enum_Type
         then
            Make_Unsignedbv_Type
           (ASVAT.Size_Model.Static_Size
                (Component_Type (Destination_Type)))
         else
            Component_Pre_Dest);

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
   begin
      for I in 0 .. Dest_High - Dest_Low loop
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
   end Copy_Array_With_Offset_Static;

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

      Loop_Inc : constant Irep := Inc_Index (Loop_Var);

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
            New_Type       => Index_T,
            A_Symbol_Table => Global_Symbol_Table),
         Lhs             =>
            Typecast_If_Necessary
           (Expr           => Index,
            New_Type       => Index_T,
            A_Symbol_Table =>
               Global_Symbol_Table),
         Source_Location => Location,
         Overflow_Check  => False,
         I_Type          => Index_T,
         Range_Check     => False));

   function Make_Zero_Index (Index : Irep; First : Int; Location : Irep)
                             return Irep is
     (Make_Zero_Index
        (Index    => Index,
         First    => Integer_Constant_To_Expr
           (Value           => UI_From_Int (First),
            Expr_Type       => Index_T,
            Source_Location => Location),
         Location => Location));

end Arrays.Low_Level;
