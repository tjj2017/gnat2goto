with Atree;             use Atree;
with Snames;            use Snames;
with Einfo;             use Einfo;
with Sinfo;             use Sinfo;

with Ireps;             use Ireps;
with Types;             use Types;

with Symbol_Table_Info; use Symbol_Table_Info;
with GOTO_Utils;        use GOTO_Utils;

package Arrays is

   procedure Add_Array_Friends (Array_Name : String;
                                Array_Type : Entity_Id;
                                Param_List : Irep)
     with Pre => (Is_Array_Type (Array_Type) and then
          not Is_Constrained (Array_Type)) and
          Kind (Param_List) = I_Parameter_List;
   --  For an unconstrained array parameter adds the array friend variables
   --  Array_Name___first_<Dimension> and Array_Name___last_<Dimension>
   --  to the subprogram parameter list for each dimension of the array.

   procedure Declare_Array_Friends (Array_Name : String;
                                    Array_Type : Entity_Id;
                                    Block      : Irep)
     with Pre => (Is_Array_Type (Array_Type) and then
          not (Is_Constrained (Etype (Array_Type)))) and
          Kind (Block) = I_Code_Block;
   --  An unconstrained array object declaration has to be suplemented
   --  by the declaration of the array friend variables
   --  Array_Name___first_<Dimension> and Array_Name___last_<Dimension>
   --  for each dimension of the array.

   function All_Dimensions_Static (The_Array : Entity_Id) return Boolean
     with Pre => Is_Array_Type (The_Array);

   function Do_Aggregate_Literal_Array (N : Node_Id) return Irep
     with Pre  => Nkind (N) = N_Aggregate;

   procedure Do_Array_Object_Declaration (Block       : Irep;
                                          Target_Def  : Entity_Id;
                                          Target_Type : Entity_Id;
                                          Array_Name  : String;
                                          Init_Expr   : Node_Id)

     with Pre => Is_Array_Type (Target_Type) and
                 Is_Array_Type (Etype (Init_Expr));
   --  In goto an array is not a type, objects may be arrays.
   --  Array types are entered into the global symbol. Some of these may
   --  be anonomous types introduced by the gnat front-end.
   --  If the object is a constrained array type then the type entry from
   --  the symbol table is used to define the goto array object.
   --  If the object is an unconstrained array subtype, then its first, last
   --  and length attributes must be determined from its mandatory
   --  initialization.  In such cases, if the initalization has a constrained
   --  subtype, then it is used to define the goto array object.
   --  If the initialization is not constrained it will not have a constrained
   --  subtype in the global symbol table and cannot be used to define the
   --  object.  In such cases the first, last and length attributes object
   --  have to be determined directly from the initialization expression
   --  and are use to define a goto array object of the correct length.

   function Do_Array_Subtype (Subtype_Node   : Node_Id;
                              Parent_Type    : Entity_Id;
                              Is_Constrained : Boolean;
                              First_Index    : Node_Id;
                              Block : Irep) return Irep
     with Pre => Is_Array_Type (Parent_Type),
     Post => Kind (Do_Array_Subtype'Result) = I_Array_Type;
   --  Create an array subtype.  If the array subtype is constrained
   --  but the constraint is not static a new variable is declared
   --  and intialised to the goto expression representing the length of the
   --  array.  This is used to specify the array length of the subtype.
   --  This is required because cbmc does not accept a general expression
   --  for the array length specifier.
   --  The declaration and intialisation of the new variable is appended
   --  to the Block.

   function Do_Constrained_Array_Definition (N     : Node_Id;
                                             Block : Irep) return Irep
     with Pre  => Nkind (N) in N_Array_Type_Definition,
     Post => Kind (Do_Constrained_Array_Definition'Result) = I_Array_Type;

   function Do_Unconstrained_Array_Definition (N : Node_Id) return Irep
     with Pre  => Nkind (N) in N_Array_Type_Definition,
     Post => Kind (Do_Unconstrained_Array_Definition'Result) =
     I_Array_Type;

   function Do_Array_Assignment (N : Node_Id) return Irep
     with Pre => Nkind (N) = N_Assignment_Statement,
     Post => Kind (Do_Array_Assignment'Result) = I_Code_Assign;

   function Do_Array_First_Last_Length (N : Node_Id; Attr : Attribute_Id)
                                        return Irep
     with Pre => Nkind (N) = N_Attribute_Reference and then
                 Attr in Attribute_First | Attribute_Last | Attribute_Length;

   function Do_Array_Length (N : Node_Id) return Irep
     with Pre => Nkind (N) = N_Attribute_Reference;

   function Do_Array_First (N : Node_Id) return Irep
     with Pre => Nkind (N) = N_Attribute_Reference;

   function Do_Array_Last (N : Node_Id) return Irep
     with Pre => Nkind (N) = N_Attribute_Reference;

   function Get_Array_Component_Type (N : Node_Id) return Entity_Id
     with Post => Is_Type (Get_Array_Component_Type'Result);

   function Do_Slice (N : Node_Id) return Irep
     with Pre  => Nkind (N) = N_Slice;

   function Do_Indexed_Component (N : Node_Id) return Irep
     with Pre  => Nkind (N) = N_Indexed_Component;

   function Get_Data_Component_From_Type (Array_Struct_Type : Irep)
                                          return Irep
     with Pre => Kind (Array_Struct_Type) in I_Array_Type,
     Post => Kind (Get_Type (Get_Data_Component_From_Type'Result))
       in I_Pointer_Type;

   function Get_First_Index (Array_Struct : Irep) return Irep
     with Pre => (Kind (Array_Struct) in Class_Expr
                  and then Kind (Get_Type (Array_Struct)) in
                    I_Symbol_Type | I_Struct_Type),
     Post => Kind (Get_First_Index'Result) = I_Member_Expr;

   function Get_Last_Index (Array_Struct : Irep) return Irep
     with Pre => (Kind (Array_Struct) in Class_Expr
                  and then Kind (Get_Type (Array_Struct)) in
                    I_Symbol_Type | I_Struct_Type),
     Post => Kind (Get_Last_Index'Result) = I_Member_Expr;

   function Get_Data_Member (Array_Struct : Irep;
                             A_Symbol_Table : Symbol_Table)
                             return Irep
     with Pre => (Kind (Array_Struct) in Class_Expr
                  and then Kind (Get_Type (Array_Struct)) in
                    I_Symbol_Type | I_Struct_Type),
       Post => Kind (Get_Data_Member'Result) = I_Member_Expr;

   function Get_Non_Array_Component_Type (A : Entity_Id) return Entity_Id
     with Pre => Is_Array_Type (A);
   --  When presented with an array repeatedly obtains the component
   --  type of the array until the component type is not an array subtype.
   --  It returns this component type.

   function Get_Underlying_Array_From_Slice (N : Node_Id) return Node_Id
     with Pre => Nkind (N) = N_Slice;

   function Offset_Array_Data (Base : Irep; Offset : Irep) return Irep
     with Pre => (Kind (Base) in Class_Expr
                  and then Kind (Offset) in Class_Expr),
     Post => Kind (Offset_Array_Data'Result) in Class_Expr;

   function Make_Array_Default_Initialiser (E : Entity_Id) return Irep;

   procedure Pass_Array_Friends (Actual_Array : Entity_Id;  Args : Irep)
     with Pre => Is_Array_Type (Etype (Actual_Array));

private

   function Do_RHS_Array_Assign (N : Node_Id) return Irep_Array
     with Pre => Nkind (N) in N_Subexpr;

   function Make_Array_First_Expr
     (Base_Type : Node_Id; Base_Irep : Irep) return Irep;

   function Build_Array_Size (First : Irep; Last : Irep; Idx_Type : Irep)
                              return Irep
     with Pre => (Kind (First) in Class_Expr
                  and Kind (Last) in Class_Expr
                  and Kind (Idx_Type) in Class_Type),
     Post => Kind (Build_Array_Size'Result) = I_Op_Add;

   function Get_First_Index_Component (Array_Struct : Irep)
                                       return Irep;

   function Get_Last_Index_Component (Array_Struct : Irep) return Irep;

   function Get_Data_Component (Array_Struct : Irep;
                                A_Symbol_Table : Symbol_Table) return Irep
     with Pre => (Kind (Array_Struct) in Class_Expr
                  and then Kind (Get_Type (Array_Struct)) in
                    I_Symbol_Type | I_Struct_Type),
     Post => Kind (Get_Type (Get_Data_Component'Result)) = I_Pointer_Type;

end Arrays;
