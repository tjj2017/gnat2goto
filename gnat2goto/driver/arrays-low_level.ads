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

   procedure Assign_To_Array_Component (Block      : Irep;
                                        The_Array  : Irep;
                                        Zero_Index : Irep;
                                        Value_Expr : Irep;
                                        I_Type     : Irep;
                                        Location   : Irep);
   --  Assigns a value (Value_Expr, to an array element specified by the
   --  zero based index (Zero_Index).

--     procedure Assign_Value_To_Dynamic_Array_Components
--       (Block            : Irep;
--        The_Array        : Irep;
--        Zero_Based_First : Irep;
--        Zero_Based_Last  : Irep;
--        Value_Expr       : Irep;
--        I_Type           : Irep;
--        Location         : Irep);

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

   function Get_Bounds (Index : Node_Id) return Dimension_Bounds;
   --  If the array is constrained, returns the lower and upper bounds of
   --  the index constraint.

   function Get_Range (Index : Node_Id) return Node_Id;

   function Make_Zero_Index (Index, First, Location : Irep) return Irep;
   --  Calculate a zero offset index from variables represented as Ireps.
   function Make_Zero_Index (Index : Irep; First : Int; Location : Irep)
                             return Irep;
   --  Calculate a zero offset index from an Ada index represented as an Irep
   --  and the lower bound given as an Int constant.

end Arrays.Low_Level;
