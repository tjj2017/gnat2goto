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

   type Static_And_Dynamic_Bounds is record
      Is_Unconstrained          : Boolean;
      Has_Static_Bounds         : Boolean;
      Low_Static, High_Static   : Int;
      Low_Dynamic, High_Dynamic : Irep;
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
         Source_Location => Get_Source_Location (Ix),
         I_Type          => Index_T));

   function Dec_Index (Ix : Irep) return Irep is
     (Make_Op_Sub
        (Rhs             => Index_T_One,
         Lhs             => Ix,
         Source_Location => Get_Source_Location (Ix),
         I_Type          => Index_T));

   function All_Dimensions_Static (The_Array : Entity_Id) return Boolean
     with Pre => Is_Array_Type (The_Array);

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

   function Calculate_Index_Offset (Array_Node  : Node_Id;
                                    The_Indices : Node_Id) return Irep
     with Pre => (Nkind (Array_Node) in N_Has_Entity and then
                      Is_Array_Type (Etype (Array_Node))) and
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

   procedure Check_Equal_Array_Lengths
     (Block         : Irep;
      Source_Bounds : Static_And_Dynamic_Bounds;
      Dest_Bounds   : Static_And_Dynamic_Bounds);

   procedure Copy_Array (Block          : Irep;
                         Source_Type    : Entity_Id;
                         Dest_Bounds    : Static_And_Dynamic_Bounds;
                         Source_Bounds  : Static_And_Dynamic_Bounds;
                         Dest_Irep      : Irep;
                         Source_Irep    : Irep)
     with Pre => Is_Array_Type (Source_Type) and
                 Kind (Get_Type (Dest_Irep))   = I_Array_Type and
                 Kind (Get_Type (Source_Irep)) = I_Array_Type;

   function Get_Bounds (Index : Node_Id) return Dimension_Bounds;
   --  If the array is constrained, returns the lower and upper bounds of
   --  the index constraint.

   function Get_Constrained_Subtype (N : Node_Id) return Entity_Id;
   --  Determines the constrained array subtype of an array expression.
   --  If no constrained subtype is found returns the unconstrained
   --  type of the expression.

   function Get_Dimension_Bounds (N : Node_Id; Dim : Positive; Index : Node_Id)
                                  return Dimension_Bounds
     with Pre => (case Nkind (N) is
                     when N_Object_Declaration |
                          N_Object_Renaming_Declaration =>
                        Is_Array_Type (Etype (Defining_Identifier (N))),
                     when N_Subtype_Declaration | N_Full_Type_Declaration =>
                        Is_Array_Type (Defining_Identifier (N)) and
                        Is_Constrained (Defining_Identifier (N)),
                     when others =>
                        Is_Array_Type (Etype (N)) and
                        Is_Constrained (Etype (N)));
   --  Returns the bounds of a dimension of an array - the array may be of
   --  unconstrained type but then N must refer to a (constrained) object.

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

   function Multi_Dimension_Flat_Bounds (Array_Node : Node_Id)
                                         return Static_And_Dynamic_Bounds
     with Pre => ((Nkind (Array_Node) in N_Full_Type_Declaration |
                                      N_Subtype_Declaration and then
                      Is_Array_Type (Defining_Identifier (Array_Node)))
               or else (Nkind (Array_Node) in N_Object_Declaration |
                      N_Object_Renaming_Declaration and then
                 Is_Array_Type (Etype (Defining_Identifier (Array_Node))))
               or else (Nkind (Array_Node) in N_Has_Etype and then
                      Is_Array_Type (Etype (Array_Node))));
   --  In goto Ada multidimensional arrays are flattenned into one dimensional
   --  arrays. This function calculates the zero based bounds of a flattened
   --  multi-dimentional array

   function Zero_Based_Bounds (The_Array : Node_Id)
                               return Static_And_Dynamic_Bounds
     with Pre => Is_Array_Type (Etype (The_Array));
   --  Calculate the zero based bounds of an array taking in to account
   --  any adjustment required if The_Array is a slice.
   --  For a slice Indexing is performed on the underlying array on which the
   --  slice is defined.
   --  If The_Array is not constrained then the result is
   --  Static_And_Dynamic_Bounds'
   --  (Is_Unconstrained  => True,
   --   Has_Static_Bounds => False,
   --   Low_Static  | High_Static  => 0,
   --   Low_Dynamic | High_Dynamic => Ireps.Empty).
   --  If the array, and any underlying array, if it is a slice, have static
   --  bounds, then result is
   --  If The_Array is not constrained then the result is
   --  Static_And_Dynamic_Bounds'
   --  (Is_Unconstrained  => False,
   --   Has_Static_Bounds => True,
   --   Low_Static   => <zero based lower bound with any slice adjustment>,
   --   High_Static  => <zero based upper bound with any slice
   --                    and multi-dimension adjustment>,
   --   Low_Dynamic  => <Irep representation of Low_Static>,
   --   High_Dynamic => <Irep representaion of High_Static>).
   --  If the array is constrained but does not have static bounds the
   --  the result is
   --  Static_And_Dynamic_Bounds'
   --  (Is_Unconstrained  => False,
   --   Has_Static_Bounds => False,
   --   Low_Static   => 0,
   --   High_Static  => 0,
   --   Low_Dynamic  => <zero based lower bound with any slice adjustment>,
   --   High_Dynamic => <zero based upper bound with any slice
   --                    and multi-dimension adjustment>.

   function Zero_Based_Slice_Bounds (The_Slice        : Node_Id;
                                     Underlying_Array : Entity_Id)
                                     return Static_And_Dynamic_Bounds
   with Pre => (Nkind (The_Slice) = N_Slice and
                Is_Array_Type (Underlying_Array));
   --  A slice is represented by its underlying array with the zero based
   --  lower and upper bounds adjusted so that they index into just the
   --  components defined by the slice.
   --  A slice is always one-dimensional and is constrained and its underlying
   --  array also must have a constraint even if it is of an unconstrained
   --  subtype.  At some point it will have been initialized and constrained.

end Arrays.Low_Level;
