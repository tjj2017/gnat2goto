with Uintp;              use Uintp;
package Arrays.Low_Level is
   --  The subprograms this package are not intended for use at the
   --  Tree_Walk package level, rather they ar intended to be used by the
   --  parent Arrays package and the Aggregates package.
   --
   --  The subprograms are concerned with manipulating the low-level, zero
   --  based array representation used by ASVAT.

   --  Type for gathering the lower and upper bounds of an array dimension.
   type Dimension_Bounds is record
      Low, High : Irep;
   end record;

   --  The type used for index expressions.
   Index_T      : constant Irep := Int64_T;

   function Index_T_Zero return Irep renames Get_Int64_T_Zero;
   function Index_T_One  return Irep is
     (Integer_Constant_To_Expr (Uint_1, Index_T, Internal_Source_Location));

   function Inc_Index (Ix : Irep) return Irep is
     (Make_Op_Add
        (Rhs             => Index_T_One,
         Lhs             => Ix,
         Source_Location => Internal_Source_Location,
         I_Type          => Index_T));

   function Dec_Index (Ix : Irep) return Irep is
     (Make_Op_Sub
        (Rhs             => Index_T_One,
         Lhs             => Ix,
         Source_Location => Internal_Source_Location,
         I_Type          => Index_T));

   procedure Assign_To_Array_Component (Block      : Irep;
                                        The_Array  : Irep;
                                        Zero_Index : Irep;
                                        Value_Expr : Irep;
                                        I_Type     : Irep;
                                        Location   : Irep);
   --  Assigns a value (Value_Expr, to an array element specified by the
   --  zero based index (Zero_Index).

   procedure Assign_Value_To_Dynamic_Array_Components
     (Block            : Irep;
      The_Array        : Irep;
      Zero_Based_First : Irep;
      Zero_Based_Last  : Irep;
      Value_Expr       : Irep;
      I_Type           : Irep;
      Location         : Irep);
   --  Assigns a single value to a contiguous set of elements of the array
   --  specified by the Zero_Based_First and Last values represented by Ireps.

   procedure Assign_Value_To_Static_Array_Components
     (Block            : Irep;
      The_Array        : Irep;
      Zero_Based_First : Int;
      Zero_Based_Last  : Int;
      Value_Expr       : Irep;
      I_Type           : Irep;
      Location         : Irep);
   --  Assigns a single value to a contiguous set of elements of the array
   --  specified by the statically determinable Zero_Based_First and Last
   --  Int values.

   function Calculate_Concat_Bounds
     (Target_Type   : Entity_Id;
      Concat_Length : Irep) return Dimension_Bounds
     with Pre => Is_Array_Type (Target_Type);
   --  Calculates the bounds of an array concatination.

   function Calculate_Concat_Length (N : Node_Id) return Irep
     with Pre => Nkind (N) = N_Op_Concat;
   --  Calculates the length of an array concatination.

   function Calculate_Dimension_Length (Bounds : Dimension_Bounds) return Irep;

   function Calculate_Index_Offset (The_Array   : Entity_Id;
                                    The_Indices : Node_Id) return Irep
     with Pre => Is_Array_Type (The_Array) and
          Nkind (The_Indices) = N_Indexed_Component;
   --  Calculates the zero based index of a possibly multidimensional
   --  Ada array. Multidimensional Ada arrays are modelled as a
   --  one-dimensional array in row major order in ASVAT.

   function Calculate_Static_Dimension_Length (Dim_Range : Node_Id)
                                               return Uint;
   --  This function can be used to calculate the length of a dimension
   --  if it is known that the dimension bounds are static.

   function Calculate_Zero_Offset (Given_Index : Node_Id;
                                   Dim_Bounds  : Dimension_Bounds) return Irep
     with Pre => Nkind (Given_Index) in N_Subexpr;
   --  Calculates the zero offset from an Index represented by an Atree node.

   procedure Copy_Array_Dynamic
     (Block            : Irep;
      Destination_Type : Entity_Id;
      Source_Type      : Entity_Id;
      Zero_Based_High  : Irep;
      Dest_Irep        : Irep;
      Source_Irep      : Irep)
     with Pre => Is_Array_Type (Destination_Type) and
                 Is_Array_Type (Source_Type) and
                 Kind (Get_Type (Dest_Irep))   = I_Array_Type and
                 Kind (Get_Type (Source_Irep)) = I_Array_Type;

   procedure Copy_Array_Static
     (Block            : Irep;
      Destination_Type : Entity_Id;
      Source_Type      : Entity_Id;
      Zero_Based_High  : Int;
      Dest_Irep        : Irep;
      Source_Irep      : Irep)
     with Pre => Is_Array_Type (Destination_Type) and
                 Is_Array_Type (Source_Type) and
                 Kind (Get_Type (Dest_Irep))   = I_Array_Type and
                 Kind (Get_Type (Source_Irep)) = I_Array_Type;

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
     with Pre => Is_Array_Type (Destination_Type) and
                 Is_Array_Type (Source_Type);

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
     with Pre => Is_Array_Type (Destination_Type) and
                 Is_Array_Type (Source_Type) and
                 Kind (Get_Type (Dest_Irep))   = I_Array_Type and
                 Kind (Get_Type (Source_Irep)) = I_Array_Type and
                 Dest_High - Dest_Low + 1 = Source_High - Source_Low + 1;

   function Get_Bounds (Index : Node_Id) return Dimension_Bounds;
   --  If the array is constrained, returns the lower and upper bounds of
   --  the index constraint.

   function Get_Constrained_Subtype (N : Node_Id) return Entity_Id;
   --  Determines the constrained array subtype of an array expression.
   --  If no constrained subtype is found returns the unconstrained
   --  type of the expression.

   function Get_Range (Index : Node_Id) return Node_Id;

   function Make_Simple_For_Loop (Loop_Var,  --  The loop variable
                                  First,     --  The initial value of loop var
                                  Last,      --  The final value of loop var
                                  Loop_Body, --  The body, using loop var
                                  Source_Location : Irep) return Irep;

   function Make_Zero_Index (Index, First, Location : Irep) return Irep;
   --  Calculate a zero offset index from variables represented as Ireps.
   function Make_Zero_Index (Index : Irep; First : Int; Location : Irep)
                             return Irep;
   --  Calculate a zero offset index from an Ada index represented as an Irep
   --  and the lower bound given as an Int constant.

end Arrays.Low_Level;
